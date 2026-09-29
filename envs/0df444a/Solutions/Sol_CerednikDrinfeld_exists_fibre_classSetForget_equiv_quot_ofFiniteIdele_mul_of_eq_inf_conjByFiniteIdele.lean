-- Prove2me | solution 1 for CerednikDrinfeld.exists_fibre_classSetForget_equiv_quot_ofFiniteIdele_mul_of_eq_inf_conjByFiniteIdele
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/30c40f72-71ad-55bb-a664-79f4d2422c59

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_Submodule_ofFiniteIdele_eq_ofFiniteIdele_iff
import Theorems.Thm_Submodule_ofFiniteIdele_diagonal_mul
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_fibre_classSetForget_equiv_quot_ofFiniteIdele_mul_of_eq_inf_conjByFiniteIdele

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra CerednikDrinfeld IsDedekindDomain

noncomputable section

namespace C1aFibre

variable {a b : ℚ}

theorem classSetForget_mk {U U' : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (h : U ≤ U') (y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    classSetForget U U' (ClassSet.mk U y) = ClassSet.mk U' y := by
  unfold classSetForget
  obtain ⟨δ, r, hδ, hr, hout⟩ :=
    DoubleCoset.mk_out_eq_mul (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range U y
  rw [show (ClassSet.mk U y).out = δ * y * r from hout]
  obtain ⟨δ', rfl⟩ := MonoidHom.mem_range.mp hδ
  rw [mul_assoc, ClassSet.mk_diagonal_mul, ClassSet.mk_mul_of_mem _ _ (h hr)]

theorem mem_localBox_conjByFiniteIdele_iff_conj_mem
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    x ∈ Submodule.localBox (Submodule.conjByFiniteIdele Λ m) v ↔
      ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom m)⁻¹ :
          (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) * x *
        (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom m :
          (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) ∈ Submodule.localBox Λ v := by
  set M := Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom m with hM
  have hMv : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (m : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
      (M : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) := by simp [hM]
  have hMv' : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v
      ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
      ((M⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) := by
    simp [hM, Units.coe_map_inv]
  rw [Submodule.mem_localBox_conjByFiniteIdele_iff Λ hΛ.fg hΛ.spanTop m v x, hMv, hMv']
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [show ((M⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) *
        ((M : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * y * ((M⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : _)) *
        (M : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = y by
      simp only [← mul_assoc, Units.inv_mul, one_mul, Units.inv_mul_cancel_right]]
  · intro h
    refine ⟨_, h, ?_⟩
    simp only [← mul_assoc, Units.mul_inv, one_mul, Units.mul_inv_cancel_right]

theorem mem_finiteIdeleStabilizer_meetOrder_iff
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    (m u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer (meetOrder Λ m) ↔
      u ∈ Submodule.finiteIdeleStabilizer Λ ∧ m⁻¹ * u * m ∈ Submodule.finiteIdeleStabilizer Λ := by
  have hc : IsOrder (Submodule.conjByFiniteIdele Λ m) := IsOrder.conjByFiniteIdele Λ hΛ m
  have hR : IsOrder (meetOrder Λ m) := hΛ.inf hc
  rw [IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits _ hR,
    IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits _ hΛ,
    IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits _ hΛ,
    ← forall_and]
  refine forall_congr' fun v => ?_
  simp only [Submodule.mem_localBoxUnits_iff, meetOrder,
    Submodule.localBox_inf Λ (Submodule.conjByFiniteIdele Λ m) hΛ.fg hΛ.spanTop hc.fg hc.spanTop v,
    AddSubgroup.coe_inf, Set.mem_inter_iff, map_mul, map_inv, Units.val_mul, mul_inv_rev, inv_inv,
    SetLike.mem_coe]
  rw [mem_localBox_conjByFiniteIdele_iff_conj_mem Λ hΛ m v,
    mem_localBox_conjByFiniteIdele_iff_conj_mem Λ hΛ m v]
  simp only [mul_assoc]
  tauto

theorem exists_fibre_classSetForget_equiv_quot
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    (U_R : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (m x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hU : ∀ u, u ∈ U_R ↔ u ∈ Submodule.finiteIdeleStabilizer Λ ∧
      m⁻¹ * u * m ∈ Submodule.finiteIdeleStabilizer Λ) :
    ∃ e : {c : ClassSet U_R // classSetForget U_R (Submodule.finiteIdeleStabilizer Λ) c =
              ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) x} ≃
            Quot (fun J J' : {J : Submodule ℤ ℍ[ℚ, a, b] //
        ∃ u ∈ Submodule.finiteIdeleStabilizer Λ, J = Submodule.ofFiniteIdele Λ (x * u * m)} =>
      ∃ δ : (ℍ[ℚ, a, b])ˣ,
        x⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x ∈ Submodule.finiteIdeleStabilizer Λ ∧
        (J' : Submodule ℤ ℍ[ℚ, a, b]) = δ • (J : Submodule ℤ ℍ[ℚ, a, b])),
      ∀ (u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hu : u ∈ Submodule.finiteIdeleStabilizer Λ)
        (hc : classSetForget U_R (Submodule.finiteIdeleStabilizer Λ) (ClassSet.mk U_R (x * u)) =
              ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) x),
        e ⟨ClassSet.mk U_R (x * u), hc⟩ =
          Quot.mk _ ⟨Submodule.ofFiniteIdele Λ (x * u * m), u, hu, rfl⟩ := by
  classical

  have hfg := hΛ.fg
  have hsp := hΛ.spanTop
  have hle : U_R ≤ Submodule.finiteIdeleStabilizer Λ := fun u hu => ((hU u).1 hu).1

  have hK : ∀ (g r : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
      m⁻¹ * r * m ∈ Submodule.finiteIdeleStabilizer Λ →
      Submodule.ofFiniteIdele Λ (g * r * m) = Submodule.ofFiniteIdele Λ (g * m) := by
    intro g r hr
    rw [Submodule.ofFiniteIdele_eq_ofFiniteIdele_iff Λ hfg hsp]
    have : (g * r * m)⁻¹ * (g * m) = (m⁻¹ * r * m)⁻¹ := by group
    rw [this]
    exact inv_mem hr

  have hKiff : ∀ {u u' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ},
      u ∈ Submodule.finiteIdeleStabilizer Λ → u' ∈ Submodule.finiteIdeleStabilizer Λ →
      (Submodule.ofFiniteIdele Λ (x * u * m) = Submodule.ofFiniteIdele Λ (x * u' * m) ↔
        u⁻¹ * u' ∈ U_R) := by
    intro u u' hu hu'
    rw [Submodule.ofFiniteIdele_eq_ofFiniteIdele_iff Λ hfg hsp, hU]
    have : (x * u * m)⁻¹ * (x * u' * m) = m⁻¹ * (u⁻¹ * u') * m := by group
    rw [this]
    exact ⟨fun h => ⟨mul_mem (inv_mem hu) hu', h⟩, fun h => h.2⟩
  have hfib : ∀ u ∈ Submodule.finiteIdeleStabilizer Λ,
      classSetForget U_R (Submodule.finiteIdeleStabilizer Λ) (ClassSet.mk U_R (x * u)) =
        ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) x := fun u hu => by
    rw [classSetForget_mk hle, ClassSet.mk_mul_of_mem _ _ hu]

  let g₀ : {J : Submodule ℤ ℍ[ℚ, a, b] //
        ∃ u ∈ Submodule.finiteIdeleStabilizer Λ, J = Submodule.ofFiniteIdele Λ (x * u * m)} →
      {c : ClassSet U_R // classSetForget U_R (Submodule.finiteIdeleStabilizer Λ) c =
        ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) x} := fun J =>
    ⟨ClassSet.mk U_R (x * Classical.choose J.2), hfib _ (Classical.choose_spec J.2).1⟩
  have hg₀ : ∀ (u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
      (_ : u ∈ Submodule.finiteIdeleStabilizer Λ) (J : {J : Submodule ℤ ℍ[ℚ, a, b] //
        ∃ u ∈ Submodule.finiteIdeleStabilizer Λ, J = Submodule.ofFiniteIdele Λ (x * u * m)}),
      (J : Submodule ℤ ℍ[ℚ, a, b]) = Submodule.ofFiniteIdele Λ (x * u * m) →
      ((g₀ J : {c : ClassSet U_R // classSetForget U_R (Submodule.finiteIdeleStabilizer Λ) c =
        ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) x}) : ClassSet U_R) =
        ClassSet.mk U_R (x * u) := by
    intro u hu J hJ
    have hu₀ := (Classical.choose_spec J.2).1
    have hJ₀ := (Classical.choose_spec J.2).2
    have hmem : (Classical.choose J.2)⁻¹ * u ∈ U_R := (hKiff hu₀ hu).1 (hJ₀.symm.trans hJ)
    show ClassSet.mk U_R (x * Classical.choose J.2) = ClassSet.mk U_R (x * u)
    calc ClassSet.mk U_R (x * Classical.choose J.2)
        = ClassSet.mk U_R (x * Classical.choose J.2 * ((Classical.choose J.2)⁻¹ * u)) :=
          (ClassSet.mk_mul_of_mem _ _ hmem).symm
      _ = ClassSet.mk U_R (x * u) := by congr 1; group

  have hwd : ∀ J J' : {J : Submodule ℤ ℍ[ℚ, a, b] //
        ∃ u ∈ Submodule.finiteIdeleStabilizer Λ, J = Submodule.ofFiniteIdele Λ (x * u * m)}, (∃ δ : (ℍ[ℚ, a, b])ˣ,
        x⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x ∈ Submodule.finiteIdeleStabilizer Λ ∧
        (J' : Submodule ℤ ℍ[ℚ, a, b]) = δ • (J : Submodule ℤ ℍ[ℚ, a, b])) → g₀ J = g₀ J' := by
    intro J J' hJJ'
    obtain ⟨δ, hδ, hJ'⟩ := hJJ'
    obtain ⟨u, hu, hJ⟩ := J.2
    have hJ'' : (J' : Submodule ℤ ℍ[ℚ, a, b]) =
        Submodule.ofFiniteIdele Λ (x * (x⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x * u) * m) := by
      rw [hJ', hJ, ← Submodule.ofFiniteIdele_diagonal_mul]
      congr 1; group
    apply Subtype.ext
    rw [hg₀ u hu J hJ, hg₀ _ (mul_mem hδ hu) J' hJ'']
    rw [show x * (x⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x * u) =
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * (x * u) by group, ClassSet.mk_diagonal_mul]
  let g : Quot (fun J J' : {J : Submodule ℤ ℍ[ℚ, a, b] //
        ∃ u ∈ Submodule.finiteIdeleStabilizer Λ, J = Submodule.ofFiniteIdele Λ (x * u * m)} =>
      ∃ δ : (ℍ[ℚ, a, b])ˣ,
        x⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x ∈ Submodule.finiteIdeleStabilizer Λ ∧
        (J' : Submodule ℤ ℍ[ℚ, a, b]) = δ • (J : Submodule ℤ ℍ[ℚ, a, b])) →
      {c : ClassSet U_R // classSetForget U_R (Submodule.finiteIdeleStabilizer Λ) c =
        ClassSet.mk (Submodule.finiteIdeleStabilizer Λ) x} := Quot.lift g₀ hwd
  have hinj : Function.Injective g := by
    rintro ⟨J⟩ ⟨J'⟩ h
    obtain ⟨u, hu, hJ⟩ := J.2
    obtain ⟨u', hu', hJ'⟩ := J'.2
    have h1 : ClassSet.mk U_R (x * u) = ClassSet.mk U_R (x * u') := by
      have := congrArg Subtype.val h
      change ((g₀ J : _) : ClassSet U_R) = ((g₀ J' : _) : ClassSet U_R) at this
      rwa [hg₀ u hu J hJ, hg₀ u' hu' J' hJ'] at this
    obtain ⟨h₁, hh₁, rr, hrr, hxu'⟩ := (DoubleCoset.eq _ _ _ _).mp h1
    obtain ⟨δ, rfl⟩ := MonoidHom.mem_range.mp hh₁
    apply Quot.sound
    refine ⟨δ, ?_, ?_⟩
    · have hd : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ = x * u' * rr⁻¹ * u⁻¹ * x⁻¹ := by
        rw [hxu']; group
      rw [show x⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x = u' * rr⁻¹ * u⁻¹ by
        rw [hd]; group]
      exact mul_mem (mul_mem hu' (inv_mem (hle hrr))) (inv_mem hu)
    · rw [hJ', hJ, hxu', ← Submodule.ofFiniteIdele_diagonal_mul,
        hK _ rr ((hU rr).1 hrr).2]
      congr 1; group
  have hsurj : Function.Surjective g := by
    rintro ⟨c, hc⟩
    obtain ⟨y, rfl⟩ := ClassSet.mk_surjective c
    rw [classSetForget_mk hle] at hc
    obtain ⟨h₁, hh₁, u, hu, hy⟩ := (DoubleCoset.eq _ _ _ _).mp hc.symm
    obtain ⟨δ, rfl⟩ := MonoidHom.mem_range.mp hh₁
    refine ⟨Quot.mk _ ⟨Submodule.ofFiniteIdele Λ (x * u * m), u, hu, rfl⟩, Subtype.ext ?_⟩
    change ((g₀ _ : _) : ClassSet U_R) = ClassSet.mk U_R y
    rw [hg₀ u hu _ rfl, hy, mul_assoc, ClassSet.mk_diagonal_mul]
  refine ⟨(Equiv.ofBijective g ⟨hinj, hsurj⟩).symm, fun u hu hc => ?_⟩
  rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply]
  apply Subtype.ext
  change ClassSet.mk U_R (x * u) = ((g₀ _ : _) : ClassSet U_R)
  rw [hg₀ u hu _ rfl]

end C1aFibre

theorem solution
    {a b : ℚ} (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsOrder Λ₁)
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : R = Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ∃ e : {c : ClassSet (Submodule.finiteIdeleStabilizer R) //
            classSetForget (Submodule.finiteIdeleStabilizer R) (Submodule.finiteIdeleStabilizer Λ₁) c =
              ClassSet.mk (Submodule.finiteIdeleStabilizer Λ₁) x} ≃
          Quot (fun J J' : {J : Submodule ℤ ℍ[ℚ, a, b] //
              ∃ u ∈ Submodule.finiteIdeleStabilizer Λ₁, J = Submodule.ofFiniteIdele Λ₁ (x * u * m)} =>
            ∃ δ : (ℍ[ℚ, a, b])ˣ,
              x⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x ∈ Submodule.finiteIdeleStabilizer Λ₁ ∧
              (J' : Submodule ℤ ℍ[ℚ, a, b]) = δ • (J : Submodule ℤ ℍ[ℚ, a, b])),
      ∀ (u : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
        (hu : u ∈ Submodule.finiteIdeleStabilizer Λ₁)
        (hc : classSetForget (Submodule.finiteIdeleStabilizer R) (Submodule.finiteIdeleStabilizer Λ₁)
            (ClassSet.mk (Submodule.finiteIdeleStabilizer R) (x * u)) =
          ClassSet.mk (Submodule.finiteIdeleStabilizer Λ₁) x),
        e ⟨ClassSet.mk (Submodule.finiteIdeleStabilizer R) (x * u), hc⟩ =
          Quot.mk _ ⟨Submodule.ofFiniteIdele Λ₁ (x * u * m), u, hu, rfl⟩ := by
  subst hR
  exact C1aFibre.exists_fibre_classSetForget_equiv_quot Λ₁ hΛ₁ _ m x
    (fun u => C1aFibre.mem_finiteIdeleStabilizer_meetOrder_iff Λ₁ hΛ₁ m u)

end

end S_CerednikDrinfeld_exists_fibre_classSetForget_equiv_quot_ofFiniteIdele_mul_of_eq_inf_conjByFiniteIdele
end P2MW
export P2MW.S_CerednikDrinfeld_exists_fibre_classSetForget_equiv_quot_ofFiniteIdele_mul_of_eq_inf_conjByFiniteIdele (solution)
