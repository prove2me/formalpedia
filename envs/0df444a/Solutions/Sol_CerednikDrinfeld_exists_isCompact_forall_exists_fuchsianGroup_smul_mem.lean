-- Prove2me | solution 1 for CerednikDrinfeld.exists_isCompact_forall_exists_fuchsianGroup_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/03c1ded0-8b1e-5c3d-a848-92142265038c

import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_CerednikDrinfeld_det_map_eq_nrd
import Theorems.Thm_CerednikDrinfeld_exists_isCompact_finset_forall_sl
import Theorems.Thm_CerednikDrinfeld_exists_finset_forall_nrd_eq_exists_mul_unit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_isCompact_forall_exists_fuchsianGroup_smul_mem

set_option autoImplicit false

open scoped Quaternion MatrixGroups TensorProduct NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld

namespace CocompactSkel

variable {a b : ℚ}

theorem exists_isCompact_forall_sl_exists_fuchsianGroup_mul_mem
    (hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x)
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) :
    ∃ K₀ : Set (Matrix (Fin 2) (Fin 2) ℝ), IsCompact K₀ ∧
      ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∃ γ ∈ fuchsianGroup R ι,
        ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ K₀ := by
  classical

  have ha : a ≠ 0 := by
    intro ha
    have hi : (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) ≠ 0 := by
      intro h; simpa using congrArg QuaternionAlgebra.imI h
    have hsq : (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) * ⟨0, 1, 0, 0⟩ = 0 := by ext <;> simp [ha]
    exact hi ((hdiv _ hi).mul_right_eq_zero.mp hsq)
  have hb : b ≠ 0 := by
    intro hb
    have hj : (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]) ≠ 0 := by
      intro h; simpa using congrArg QuaternionAlgebra.imJ h
    have hsq : (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]) * ⟨0, 0, 1, 0⟩ = 0 := by ext <;> simp [hb]
    exact hj ((hdiv _ hj).mul_right_eq_zero.mp hsq)
  obtain ⟨C, S, hC, hmink⟩ := CerednikDrinfeld.exists_isCompact_finset_forall_sl hdiv R hR ι hι
  choose T hTR hT using fun n : ℚ => CerednikDrinfeld.exists_finset_forall_nrd_eq_exists_mul_unit hdiv R hR n

  have hinv : ∀ t : ℍ[ℚ, a, b], ∃ t' : ℍ[ℚ, a, b], t ≠ 0 → t' * t = 1 := by
    intro t
    by_cases ht : t = 0
    · exact ⟨0, fun h => (h ht).elim⟩
    · obtain ⟨w, hw⟩ := hdiv t ht
      exact ⟨(w⁻¹ : (ℍ[ℚ, a, b])ˣ), fun _ => by rw [← hw, Units.inv_mul]⟩
  choose inv hinv using hinv
  let K₀ : Set (Matrix (Fin 2) (Fin 2) ℝ) :=
    ⋃ n ∈ S, ⋃ t ∈ T n, (fun c => ι (inv t) * c) '' C
  refine ⟨K₀, ?_, ?_⟩
  · refine S.finite_toSet.isCompact_biUnion fun n _ => (T n).finite_toSet.isCompact_biUnion fun t _ => ?_
    exact hC.image (continuous_const.mul continuous_id)
  · intro g
    obtain ⟨r, hrR, hr0, hrS, hrC⟩ := hmink g
    obtain ⟨t, htT, u, hu, hu1, hrtu⟩ := hT (nrd r) r hrR rfl
    have ht0 : t ≠ 0 := by rintro rfl; exact hr0 (by rw [hrtu, zero_mul])
    obtain ⟨huR, v, hvR, huv, hvu⟩ := hu
    let uu : (ℍ[ℚ, a, b])ˣ := ⟨u, v, huv, hvu⟩
    let γ : GL (Fin 2) ℝ := Units.map (ι : ℍ[ℚ, a, b] →* Matrix (Fin 2) (Fin 2) ℝ) uu
    have hγ : γ ∈ fuchsianGroup R ι := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨uu, ?_, rfl⟩, ?_⟩
      · exact Subgroup.subset_closure ⟨huR, v, hvR, huv, hvu⟩
      · rw [MonoidHom.mem_ker]
        ext
        rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
        change (ι u).det = 1
        rw [CerednikDrinfeld.det_map_eq_nrd ha hb ι hι, hu1, Rat.cast_one]
    refine ⟨γ, hγ, ?_⟩
    have hγval : ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = ι u := rfl
    rw [hγval]
    refine Set.mem_biUnion hrS (Set.mem_biUnion htT ⟨ι r * (g : Matrix (Fin 2) (Fin 2) ℝ), hrC, ?_⟩)
    simp only
    rw [hrtu, map_mul, ← mul_assoc, ← mul_assoc, ← map_mul, hinv t ht0, map_one, one_mul]

end CocompactSkel

open CocompactSkel in

theorem solution {a b : ℚ} (hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x)
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) :
    ∃ K : Set UpperHalfPlane, IsCompact K ∧
      ∀ τ : UpperHalfPlane, ∃ γ ∈ fuchsianGroup R ι, γ • τ ∈ K := by
  obtain ⟨K₀, hK₀, hcov⟩ := exists_isCompact_forall_sl_exists_fuchsianGroup_mul_mem hdiv R hR ι hι

  let K₁ : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) := {g | (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ K₀}
  have hemb : Topology.IsClosedEmbedding
      ((↑) : Matrix.SpecialLinearGroup (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) := by
    refine Topology.IsClosedEmbedding.subtypeVal ?_
    exact isClosed_eq (Continuous.matrix_det continuous_id) continuous_const
  have hK₁ : IsCompact K₁ := hemb.isCompact_preimage hK₀
  refine ⟨(fun g : Matrix.SpecialLinearGroup (Fin 2) ℝ => g • UpperHalfPlane.I) '' K₁,
    hK₁.image (continuous_id.smul continuous_const), ?_⟩
  intro τ
  obtain ⟨g₀, hg₀⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 2) ℝ) UpperHalfPlane.I τ
  obtain ⟨γ, hγ, hmem⟩ := hcov g₀
  have hdet : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * (g₀ : Matrix (Fin 2) (Fin 2) ℝ)).det = 1 := by
    obtain ⟨-, hker⟩ := Subgroup.mem_inf.mp hγ
    have h1 : ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.mp hker)
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
    rw [Matrix.det_mul, h1, g₀.prop, one_mul]
  let g₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ := ⟨_, hdet⟩
  refine ⟨γ, hγ, g₁, hmem, ?_⟩
  rw [← hg₀]
  change (Matrix.SpecialLinearGroup.toGL g₁) • UpperHalfPlane.I =
    γ • ((Matrix.SpecialLinearGroup.toGL g₀) • UpperHalfPlane.I)
  rw [← mul_smul]
  congr 1
  ext i j
  rfl

end S_CerednikDrinfeld_exists_isCompact_forall_exists_fuchsianGroup_smul_mem
end P2MW
export P2MW.S_CerednikDrinfeld_exists_isCompact_forall_exists_fuchsianGroup_smul_mem (solution)
