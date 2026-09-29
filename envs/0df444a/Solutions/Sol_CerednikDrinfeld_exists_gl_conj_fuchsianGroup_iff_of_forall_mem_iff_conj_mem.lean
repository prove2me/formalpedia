-- Prove2me | solution 1 for CerednikDrinfeld.exists_gl_conj_fuchsianGroup_iff_of_forall_mem_iff_conj_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/bcb9950e-75ff-56c6-bd5b-630b14e8184b

import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Theorems.Thm_QuaternionAlgebra_det_eq_nrd_of_injective
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_gl_conj_fuchsianGroup_iff_of_forall_mem_iff_conj_mem

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField MatrixGroups Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

namespace FuchsNormAux

variable {a b : ℚ}

theorem nrd_mul (x y : ℍ[ℚ, a, b]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [nrd, QuaternionAlgebra.mk_mul_mk]
  ring

theorem ne_zero_and_ne_zero {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q') :
    a ≠ 0 ∧ b ≠ 0 := by
  have key : ∀ y : ℍ[ℚ, a, b], y ≠ 0 → y * y = 0 → False := by
    intro y hy hyy
    obtain ⟨u, rfl⟩ := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB y hy
    apply hy
    calc (u : ℍ[ℚ, a, b]) = ↑u⁻¹ * (↑u * ↑u) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = 0 := by rw [hyy, mul_zero]
  refine ⟨fun h0 => key ⟨0, 1, 0, 0⟩ ?_ ?_, fun h0 => key ⟨0, 0, 1, 0⟩ ?_ ?_⟩
  · intro h; simpa using congrArg QuaternionAlgebra.imI h
  · ext <;> simp [h0]
  · intro h; simpa using congrArg QuaternionAlgebra.imJ h
  · ext <;> simp [h0]

end FuchsNormAux

open FuchsNormAux in
theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (w : (ℍ[ℚ, a, b])ˣ) (hwpos : 0 < nrd (w : ℍ[ℚ, a, b]))
    (hwnorm : ∀ x : ℍ[ℚ, a, b], x ∈ R ↔ (w : ℍ[ℚ, a, b]) * x * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R) :
    ∃ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = ι (w : ℍ[ℚ, a, b]) ∧ 0 < g.det.val ∧
      (∀ γ : GL (Fin 2) ℝ, γ ∈ fuchsianGroup R ι ↔ g * γ * g⁻¹ ∈ fuchsianGroup R ι) ∧
      (∀ u : ℍ[ℚ, a, b], IsUnitOf R u → nrd u = 1 →
        ∃ γ : GL (Fin 2) ℝ, γ ∈ fuchsianGroup R ι ∧ (γ : Matrix (Fin 2) (Fin 2) ℝ) = ι u) ∧
      (∀ x : ℍ[ℚ, a, b], nrd ((w : ℍ[ℚ, a, b]) * x * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) = nrd x) := by
  classical
  obtain ⟨ha, hb⟩ := ne_zero_and_ne_zero hB
  have hdet : ∀ x : ℍ[ℚ, a, b], (ι x).det = ((nrd x : ℚ) : ℝ) := QuaternionAlgebra.det_eq_nrd_of_injective ha hb ι hι
  let ιm : ℍ[ℚ, a, b] →* Matrix (Fin 2) (Fin 2) ℝ := (ι : ℍ[ℚ, a, b] →* Matrix (Fin 2) (Fin 2) ℝ)
  let g : GL (Fin 2) ℝ := Units.map ιm w
  have hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = ι (w : ℍ[ℚ, a, b]) := rfl

  set S : Set (ℍ[ℚ, a, b])ˣ := {u : (ℍ[ℚ, a, b])ˣ | IsUnitOf R (u : ℍ[ℚ, a, b])} with hS
  have winv : ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * (w : ℍ[ℚ, a, b]) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have winv' : (w : ℍ[ℚ, a, b]) * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hconj : ∀ u : (ℍ[ℚ, a, b])ˣ, u ∈ S → w * u * w⁻¹ ∈ S := by
    intro u hu
    obtain ⟨huR, v, hvR, huv, hvu⟩ := hu
    refine ⟨(hwnorm _).mp huR, (w : ℍ[ℚ, a, b]) * v * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]), (hwnorm _).mp hvR, ?_, ?_⟩
    · show (w : ℍ[ℚ, a, b]) * u * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * ((w : ℍ[ℚ, a, b]) * v * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) = 1
      calc _ = (w : ℍ[ℚ, a, b]) * u * (((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * (w : ℍ[ℚ, a, b])) * v * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) := by
              simp only [mul_assoc]
        _ = 1 := by rw [winv, mul_one, mul_assoc (w : ℍ[ℚ, a, b]), huv, mul_one, winv']
    · show (w : ℍ[ℚ, a, b]) * v * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * ((w : ℍ[ℚ, a, b]) * u * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) = 1
      calc _ = (w : ℍ[ℚ, a, b]) * v * (((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * (w : ℍ[ℚ, a, b])) * u * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) := by
              simp only [mul_assoc]
        _ = 1 := by rw [winv, mul_one, mul_assoc (w : ℍ[ℚ, a, b]), hvu, mul_one, winv']
  have hconj' : ∀ u : (ℍ[ℚ, a, b])ˣ, u ∈ S → w⁻¹ * u * w ∈ S := by
    intro u hu
    obtain ⟨huR, v, hvR, huv, hvu⟩ := hu
    have back : ∀ x : ℍ[ℚ, a, b], x ∈ R → ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * x * (w : ℍ[ℚ, a, b]) ∈ R := by
      intro x hx
      apply (hwnorm _).mpr
      have : (w : ℍ[ℚ, a, b]) * (((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * x * (w : ℍ[ℚ, a, b])) * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = x := by
        calc _ = ((w : ℍ[ℚ, a, b]) * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) * x * ((w : ℍ[ℚ, a, b]) * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) := by
                simp only [mul_assoc]
          _ = x := by simp only [winv', one_mul, mul_one]
      rw [this]; exact hx
    refine ⟨?_, ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * v * (w : ℍ[ℚ, a, b]), back v hvR, ?_, ?_⟩
    · have := back u huR
      simpa only [Units.val_mul] using this
    · show ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * u * (w : ℍ[ℚ, a, b]) * (((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * v * (w : ℍ[ℚ, a, b])) = 1
      calc _ = ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * u * ((w : ℍ[ℚ, a, b]) * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) * v * (w : ℍ[ℚ, a, b]) := by
              simp only [mul_assoc]
        _ = 1 := by rw [winv', mul_one, mul_assoc ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]), huv, mul_one, winv]
    · show ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * v * (w : ℍ[ℚ, a, b]) * (((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * u * (w : ℍ[ℚ, a, b])) = 1
      calc _ = ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * v * ((w : ℍ[ℚ, a, b]) * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) * u * (w : ℍ[ℚ, a, b]) := by
              simp only [mul_assoc]
        _ = 1 := by rw [winv', mul_one, mul_assoc ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]), hvu, mul_one, winv]

  have hUG : ∀ u : (ℍ[ℚ, a, b])ˣ, u ∈ unitGroup R → w * u * w⁻¹ ∈ unitGroup R := by
    intro u hu
    have : unitGroup R = Subgroup.closure S := rfl
    rw [this] at hu ⊢
    rw [show w * u * w⁻¹ = MulAut.conj w u from rfl, ← MonoidHom.coe_coe, ← Subgroup.mem_comap]
    revert u hu
    rw [← SetLike.le_def, Subgroup.closure_le]
    intro u hu
    rw [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.coe_coe, MulAut.conj_apply]
    exact Subgroup.subset_closure (hconj u hu)
  have hUG' : ∀ u : (ℍ[ℚ, a, b])ˣ, u ∈ unitGroup R → w⁻¹ * u * w ∈ unitGroup R := by
    intro u hu
    have : unitGroup R = Subgroup.closure S := rfl
    rw [this] at hu ⊢
    rw [show w⁻¹ * u * w = MulAut.conj w⁻¹ u by rw [MulAut.conj_apply, inv_inv], ← MonoidHom.coe_coe, ← Subgroup.mem_comap]
    revert u hu
    rw [← SetLike.le_def, Subgroup.closure_le]
    intro u hu
    rw [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
    exact Subgroup.subset_closure (hconj' u hu)

  have hgdet : (g : Matrix (Fin 2) (Fin 2) ℝ).det = ((nrd (w : ℍ[ℚ, a, b]) : ℚ) : ℝ) := by rw [hg, hdet]
  refine ⟨g, hg, ?_, ?_, ?_, ?_⟩
  ·
    rw [Matrix.GeneralLinearGroup.val_det_apply, hgdet]
    exact_mod_cast hwpos
  ·
    intro γ
    simp only [fuchsianGroup, Subgroup.mem_inf, Subgroup.mem_map, MonoidHom.mem_ker]
    constructor
    · rintro ⟨⟨u, hu, huγ⟩, hγdet⟩
      refine ⟨⟨w * u * w⁻¹, hUG u hu, ?_⟩, ?_⟩
      · rw [← huγ, map_mul, map_mul, map_inv]
      · rw [map_mul, map_mul, map_inv, hγdet, mul_one, mul_inv_cancel]
    · rintro ⟨⟨u, hu, huγ⟩, hγdet⟩
      refine ⟨⟨w⁻¹ * u * w, hUG' u hu, ?_⟩, ?_⟩
      · rw [map_mul, map_mul, map_inv, huγ]
        show g⁻¹ * (g * γ * g⁻¹) * g = γ
        group
      · have : γ = g⁻¹ * (g * γ * g⁻¹) * g := by group
        rw [this, map_mul, map_mul, map_inv, hγdet, mul_one, inv_mul_cancel]
  ·
    intro u hu hnrd
    obtain ⟨huR, v, hvR, huv, hvu⟩ := hu
    let uu : (ℍ[ℚ, a, b])ˣ := ⟨u, v, huv, hvu⟩
    refine ⟨Units.map ιm uu, Subgroup.mem_inf.mpr ⟨⟨uu, Subgroup.subset_closure ⟨huR, v, hvR, huv, hvu⟩, rfl⟩, ?_⟩, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    show (ι u).det = 1
    rw [hdet, hnrd]; push_cast; rfl
  ·
    intro x
    rw [nrd_mul, nrd_mul, mul_comm (nrd (w : ℍ[ℚ, a, b])), mul_assoc, ← nrd_mul, winv', nrd_one, mul_one]

end S_CerednikDrinfeld_exists_gl_conj_fuchsianGroup_iff_of_forall_mem_iff_conj_mem
end P2MW
export P2MW.S_CerednikDrinfeld_exists_gl_conj_fuchsianGroup_iff_of_forall_mem_iff_conj_mem (solution)
