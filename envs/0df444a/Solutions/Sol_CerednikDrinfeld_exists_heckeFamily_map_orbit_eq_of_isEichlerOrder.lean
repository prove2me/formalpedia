-- Prove2me | solution 1 for CerednikDrinfeld.exists_heckeFamily_map_orbit_eq_of_isEichlerOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/823d0f1f-b619-5172-a799-98b61c78d66d

import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Theorems.Thm_CerednikDrinfeld_det_map_eq_nrd
import Theorems.Thm_CerednikDrinfeld_exists_finset_forall_nrd_eq_exists_mul_unit
import Theorems.Thm_QuaternionAlgebra_nrd_mul
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_Submodule_conjByFiniteIdele_mul_eq_of_mem_finiteIdeleStabilizer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_heckeFamily_map_orbit_eq_of_isEichlerOrder

set_option autoImplicit false

open scoped MatrixGroups Topology Quaternion TensorProduct NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld

section IdelicHalf

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

namespace HeckeLocal

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

def boxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ𝔸 :=
  {x | ∃ z ∈ Λ, ∃ c : FiniteAdeleRing (𝓞 ℚ) ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), c v ∈ v.adicCompletionIntegers ℚ) ∧ x = z ⊗ₜ[ℚ] c}

theorem box_eq_span (Λ : Submodule ℤ ℍ[ℚ, a, b]) :
    Submodule.finiteAdeleBox Λ = (Submodule.span ℤ (boxGen Λ)).toAddSubgroup := by
  rw [Submodule.span_int_eq_addSubgroupClosure]; rfl

theorem mem_box_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} {x : ℍ𝔸} :
    x ∈ Submodule.finiteAdeleBox Λ ↔ x ∈ Submodule.span ℤ (boxGen Λ) := by
  rw [box_eq_span]; rfl

theorem box_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {x y : ℍ𝔸} (hx : x ∈ Submodule.finiteAdeleBox Λ) (hy : y ∈ Submodule.finiteAdeleBox Λ) :
    x * y ∈ Submodule.finiteAdeleBox Λ := by
  rw [mem_box_iff] at hx hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      refine Submodule.subset_span ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, fun v => ?_, ?_⟩
      · have e : (c' * c) v = c' v * c v := rfl
        rw [e]
        exact mul_mem (hc' v) (hc v)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
    | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁
  | zero => rw [mul_zero]; exact zero_mem _
  | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m y₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem one_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) :
    (1 : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
  unfold Submodule.finiteAdeleBox
  refine AddSubgroup.subset_closure ⟨1, hΛ.one_mem, 1, fun v => ?_, ?_⟩
  · have e : (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := rfl
    rw [e]; exact one_mem _
  · rfl

theorem coe_mem_box_of_mem_stabilizer {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {u : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) :
    (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
  have h := (Submodule.mem_finiteIdeleStabilizer_iff Λ u).mp hu

  have h1 : (u : ℍ𝔸) * 1 ∈ u • ((Submodule.finiteAdeleBox Λ : AddSubgroup ℍ𝔸) : Set ℍ𝔸) :=
    Set.smul_mem_smul_set (one_mem_box hΛ)
  rw [h, mul_one] at h1
  exact h1

theorem coe_inv_mem_box_of_mem_stabilizer {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {u : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) :
    ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ :=
  coe_mem_box_of_mem_stabilizer hΛ (inv_mem hu)

theorem mul_mem_primeHeckeSet_of_mem_stabilizer {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (ℓ : ℕ) {u h : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) (hh : h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ) :
    u * h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ := by
  obtain ⟨h1, h2, h3, h4⟩ := hh
  have hub := coe_mem_box_of_mem_stabilizer hΛ hu
  have huib := coe_inv_mem_box_of_mem_stabilizer hΛ hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Units.val_mul]; exact box_mul_mem hΛ hub h1
  · rw [mul_inv_rev, Units.val_mul, ← smul_mul_assoc]
    exact box_mul_mem hΛ h2 huib
  · intro hmem
    apply h3
    have : ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = (((u * h)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (u : ℍ𝔸) := by
      rw [mul_inv_rev, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [this]; exact box_mul_mem hΛ hmem hub
  · intro hmem
    apply h4
    have : (ℓ : ℚ)⁻¹ • (h : ℍ𝔸) = ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((ℓ : ℚ)⁻¹ • ((u * h : (ℍ𝔸)ˣ) : ℍ𝔸)) := by
      rw [mul_smul_comm, Units.val_mul, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]; exact box_mul_mem hΛ huib hmem

theorem mul_mem_primeHeckeSet_of_mem_stabilizer' {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (ℓ : ℕ) {u h : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) (hh : h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ) :
    h * u ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ := by
  obtain ⟨h1, h2, h3, h4⟩ := hh
  have hub := coe_mem_box_of_mem_stabilizer hΛ hu
  have huib := coe_inv_mem_box_of_mem_stabilizer hΛ hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Units.val_mul]; exact box_mul_mem hΛ h1 hub
  · rw [mul_inv_rev, Units.val_mul, ← mul_smul_comm]
    exact box_mul_mem hΛ huib h2
  · intro hmem
    apply h3
    have : ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = (u : ℍ𝔸) * (((h * u)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := by
      rw [mul_inv_rev, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
    rw [this]; exact box_mul_mem hΛ hub hmem
  · intro hmem
    apply h4
    have : (ℓ : ℚ)⁻¹ • (h : ℍ𝔸) = ((ℓ : ℚ)⁻¹ • ((h * u : (ℍ𝔸)ˣ) : ℍ𝔸)) * ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := by
      rw [smul_mul_assoc, Units.val_mul, mul_assoc, Units.mul_inv, mul_one]
    rw [this]; exact box_mul_mem hΛ hmem huib

theorem box_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') :
    Submodule.finiteAdeleBox Λ ≤ Submodule.finiteAdeleBox Λ' := by
  unfold Submodule.finiteAdeleBox
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem mem_stabilizer_of_coe_mem_of_coe_inv_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {u : (ℍ𝔸)ˣ} (hu : (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ) (hui : ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ := by
  rw [Submodule.mem_finiteIdeleStabilizer_iff]
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact box_mul_mem hΛ hu hx
  · intro x hx
    refine ⟨(u⁻¹ : (ℍ𝔸)ˣ) • x, box_mul_mem hΛ hui hx, ?_⟩
    show (u : ℍ𝔸) * (((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x) = x
    rw [← mul_assoc, Units.mul_inv, one_mul]

theorem stabilizer_mono {S R : Submodule ℤ ℍ[ℚ, a, b]} (hS : QuaternionAlgebra.IsOrder S) (hR : QuaternionAlgebra.IsOrder R)
    (h : S ≤ R) : Submodule.finiteIdeleStabilizer S ≤ Submodule.finiteIdeleStabilizer R := by
  intro u hu
  exact mem_stabilizer_of_coe_mem_of_coe_inv_mem hR (box_mono h (coe_mem_box_of_mem_stabilizer hS hu))
    (box_mono h (coe_inv_mem_box_of_mem_stabilizer hS hu))

theorem mem_stabilizer_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔
      (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ ∧ ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ :=
  ⟨fun hu => ⟨coe_mem_box_of_mem_stabilizer hΛ hu, coe_inv_mem_box_of_mem_stabilizer hΛ hu⟩,
   fun h => mem_stabilizer_of_coe_mem_of_coe_inv_mem hΛ h.1 h.2⟩

end HeckeLocal

namespace A2Hstab

open QuaternionAlgebra CerednikDrinfeld HeckeLocal

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

theorem tmul_one_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) :
    z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ := by
  unfold Submodule.finiteAdeleBox
  refine AddSubgroup.subset_closure ⟨z, hz, 1, fun v => ?_, rfl⟩
  have e : (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := rfl
  rw [e]; exact one_mem _

theorem diagonal_mem_stabilizer {Λ R : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (hRΛ : R ≤ Λ)
    {u : ℍ[ℚ, a, b]} (hu : IsUnitOf R u) (U : (ℍ[ℚ, a, b])ˣ) (hU : (U : ℍ[ℚ, a, b]) = u) :
    Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] U ∈ Submodule.finiteIdeleStabilizer Λ := by
  obtain ⟨huR, v, hvR, huv, hvu⟩ := hu
  have hUinv : ((U⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = v := by
    rw [← hU] at huv
    exact Units.inv_eq_of_mul_eq_one_right huv
  refine mem_stabilizer_of_coe_mem_of_coe_inv_mem hΛ ?_ ?_
  · rw [Submodule.val_finiteIdeleDiagonal_apply, hU]; exact tmul_one_mem_box (hRΛ huR)
  · rw [← map_inv, Submodule.val_finiteIdeleDiagonal_apply, hUinv]; exact tmul_one_mem_box (hRΛ hvR)

end A2Hstab

open scoped MatrixGroups Topology
open QuaternionAlgebra CerednikDrinfeld HeckeLocal A2Hstab in

theorem hstab {a b : ℚ} (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛo : IsOrder Λ) (hRo : IsOrder R)
    (hRΛ : R ≤ Λ) (N ℓ : ℕ) {u : ℍ[ℚ, a, b]} (hu : IsUnitOf R u)
    {h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hh : h ∈ (if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ)) :
    ∃ h' ∈ (if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ),
      (h' : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
        (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * ((u ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ))) := by
  obtain ⟨huR, v, hvR, huv, hvu⟩ := hu
  let U : (ℍ[ℚ, a, b])ˣ := ⟨u, v, huv, hvu⟩
  let d := Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] U
  have hdR : d ∈ Submodule.finiteIdeleStabilizer R :=
    diagonal_mem_stabilizer hRo le_rfl ⟨huR, v, hvR, huv, hvu⟩ U rfl
  have hdΛ : d ∈ Submodule.finiteIdeleStabilizer Λ :=
    diagonal_mem_stabilizer hΛo hRΛ ⟨huR, v, hvR, huv, hvu⟩ U rfl
  refine ⟨h * d, ?_, by rw [Units.val_mul, Submodule.val_finiteIdeleDiagonal_apply]⟩
  split_ifs at hh ⊢ with hℓ
  · obtain ⟨hT, hne, hnle⟩ := hh
    refine ⟨mul_mem_primeHeckeSet_of_mem_stabilizer' hRo ℓ hdR hT, ?_, ?_⟩
    · rwa [Submodule.conjByFiniteIdele_mul_eq_of_mem_finiteIdeleStabilizer R hRo.one_mem
        (fun x y hx hy => hRo.mul_mem hx hy) h d hdR]
    · rwa [Submodule.conjByFiniteIdele_mul_eq_of_mem_finiteIdeleStabilizer Λ hΛo.one_mem
        (fun x y hx hy => hΛo.mul_mem hx hy) h d hdΛ]
  · exact mul_mem_primeHeckeSet_of_mem_stabilizer' hRo ℓ hdR hh

end IdelicHalf

namespace HeckeWD

variable {a b : ℚ}

theorem isUnitOf_one {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : IsOrder R) : IsUnitOf R 1 :=
  ⟨hRo.one_mem, 1, hRo.one_mem, one_mul 1, one_mul 1⟩

theorem isUnitOf_mul {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : IsOrder R) {u v : ℍ[ℚ, a, b]}
    (hu : IsUnitOf R u) (hv : IsUnitOf R v) : IsUnitOf R (u * v) := by
  obtain ⟨huR, u', hu'R, huu', hu'u⟩ := hu
  obtain ⟨hvR, v', hv'R, hvv', hv'v⟩ := hv
  refine ⟨hRo.mul_mem huR hvR, v' * u', hRo.mul_mem hv'R hu'R, ?_, ?_⟩
  · rw [mul_assoc, ← mul_assoc v, hvv', one_mul, huu']
  · rw [mul_assoc, ← mul_assoc u', hu'u, one_mul, hv'v]

theorem nrd_inv_eq_one {u u' : ℍ[ℚ, a, b]} (huu' : u * u' = 1) (hn : nrd u = 1) : nrd u' = 1 := by
  have := QuaternionAlgebra.nrd_mul u u'
  rw [huu', nrd_one, hn, one_mul] at this
  exact this.symm

def LRel (R : Submodule ℤ ℍ[ℚ, a, b]) (x y : ℍ[ℚ, a, b]) : Prop :=
  ∃ u : ℍ[ℚ, a, b], IsUnitOf R u ∧ nrd u = 1 ∧ u * x = y

theorem LRel.refl {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : IsOrder R) (x : ℍ[ℚ, a, b]) : LRel R x x :=
  ⟨1, isUnitOf_one hRo, nrd_one, one_mul x⟩

theorem LRel.symm {R : Submodule ℤ ℍ[ℚ, a, b]} {x y : ℍ[ℚ, a, b]} (h : LRel R x y) : LRel R y x := by
  obtain ⟨u, ⟨huR, v, hvR, huv, hvu⟩, hn, hxy⟩ := h
  exact ⟨v, ⟨hvR, u, huR, hvu, huv⟩, nrd_inv_eq_one huv hn, by rw [← hxy, ← mul_assoc, hvu, one_mul]⟩

theorem LRel.trans {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : IsOrder R) {x y z : ℍ[ℚ, a, b]}
    (h₁ : LRel R x y) (h₂ : LRel R y z) : LRel R x z := by
  obtain ⟨u, hu, hnu, hxy⟩ := h₁
  obtain ⟨v, hv, hnv, hyz⟩ := h₂
  refine ⟨v * u, isUnitOf_mul hRo hv hu, by rw [QuaternionAlgebra.nrd_mul, hnv, hnu, one_mul], ?_⟩
  rw [mul_assoc, hxy, hyz]

theorem star_mem {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : IsOrder R) {y : ℍ[ℚ, a, b]} (hy : y ∈ R) :
    star y ∈ R := by
  obtain ⟨-, t, ht⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hRo hy
  have hstar : star y = ((trd y : ℚ) : ℍ[ℚ, a, b]) - y := by
    rw [← add_star_eq_coe_trd]; abel
  rw [hstar, ← ht]
  refine R.sub_mem ?_ hy
  have : ((t : ℚ) : ℍ[ℚ, a, b]) = t • (1 : ℍ[ℚ, a, b]) := by
    rw [← Int.cast_smul_eq_zsmul ℚ, Algebra.smul_def, mul_one]; rfl
  rw [this]
  exact R.smul_mem t hRo.one_mem

theorem isUnitOf_star {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : IsOrder R) {u : ℍ[ℚ, a, b]}
    (hu : IsUnitOf R u) : IsUnitOf R (star u) := by
  obtain ⟨huR, v, hvR, huv, hvu⟩ := hu
  refine ⟨star_mem hRo huR, star v, star_mem hRo hvR, ?_, ?_⟩
  · rw [← star_mul, hvu, star_one]
  · rw [← star_mul, huv, star_one]

end HeckeWD

open HeckeWD in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {N : ℕ} [NeZero N]
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) :
    ∃ H : ∀ ℓ : ℕ, ℓ.Prime → Multiset (GL (Fin 2) ℝ),
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ∃ S : Finset ℍ[ℚ, a, b],
        (∀ x ∈ S, x ∈ R ∧ nrd x = ℓ ∧
          ∃ h ∈ (if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ),
            (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = x ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) ∧
        (∀ y : ℍ[ℚ, a, b], y ∈ R → nrd y = ℓ →
          (∃ h ∈ (if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ),
            (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = y ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) →
          ∃! x, x ∈ S ∧ ∃ u : ℍ[ℚ, a, b], IsUnitOf R u ∧ nrd u = 1 ∧ u * x = y) ∧
        (H ℓ hℓ).map (fun g => (g : Matrix (Fin 2) (Fin 2) ℝ)) = S.val.map ι) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ∀ γ ∈ fuchsianGroup R ι, ∀ τ : UpperHalfPlane,
        ((H ℓ hℓ).map fun δ => MulAction.orbit ↥(fuchsianGroup R ι) (δ • γ • τ)) =
          ((H ℓ hℓ).map fun δ => MulAction.orbit ↥(fuchsianGroup R ι) (δ • τ))) := by
  classical
  have hRo : IsOrder R := hR.isOrder
  have hΛo : IsOrder Λ := hΛ.isOrder
  have hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x := fun x hx =>
    QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB x hx
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

  set 𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
    fun ℓ => if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ with h𝒮
  let P : ℕ → ℍ[ℚ, a, b] → Prop := fun ℓ y =>
    y ∈ R ∧ nrd y = (ℓ : ℚ) ∧ ∃ h ∈ 𝒮 ℓ,
      (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = y ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)

  let toGL : ℍ[ℚ, a, b] → GL (Fin 2) ℝ := fun x =>
    if hx : x = 0 then 1 else Units.map (ι : ℍ[ℚ, a, b] →* Matrix (Fin 2) (Fin 2) ℝ) (hdiv x hx).unit
  have toGL_val : ∀ x : ℍ[ℚ, a, b], x ≠ 0 →
      ((toGL x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = ι x := by
    intro x hx
    simp only [toGL, dif_neg hx, Units.coe_map, MonoidHom.coe_coe, IsUnit.unit_spec]
  have toGL_mul : ∀ x y : ℍ[ℚ, a, b], x ≠ 0 → y ≠ 0 → toGL (x * y) = toGL x * toGL y := by
    intro x y hx hy
    have hxy : x * y ≠ 0 := fun h => hy ((hdiv x hx).mul_right_eq_zero.mp h)
    ext
    rw [Units.val_mul, toGL_val _ hxy, toGL_val _ hx, toGL_val _ hy, map_mul]
  have toGL_mem : ∀ u : ℍ[ℚ, a, b], IsUnitOf R u → nrd u = 1 → toGL u ∈ fuchsianGroup R ι := by
    intro u hu hnu
    have hu0 : u ≠ 0 := by rintro rfl; simp at hnu
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨(hdiv u hu0).unit, ?_, ?_⟩, ?_⟩
    · exact Subgroup.subset_closure (by simpa [IsUnit.unit_spec] using hu)
    · simp only [toGL, dif_neg hu0]
    · rw [MonoidHom.mem_ker]
      ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, toGL_val u hu0,
        CerednikDrinfeld.det_map_eq_nrd ha hb ι hι, hnu, Rat.cast_one]

  have hΓ : ∀ γ ∈ fuchsianGroup R ι, ∃ u₀ : ℍ[ℚ, a, b], IsUnitOf R u₀ ∧ nrd u₀ = 1 ∧ u₀ ≠ 0 ∧
      γ = toGL u₀ := by
    intro γ hγ
    obtain ⟨hγmap, hker⟩ := Subgroup.mem_inf.mp hγ
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hγmap

    let U : Subgroup (ℍ[ℚ, a, b])ˣ :=
      { carrier := {v | (v : ℍ[ℚ, a, b]) ∈ R ∧ ((v⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R}
        one_mem' := ⟨by simpa using hRo.one_mem, by simpa using hRo.one_mem⟩
        mul_mem' := by
          rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
          refine ⟨by push_cast; exact hRo.mul_mem hx hy, ?_⟩
          rw [mul_inv_rev]; push_cast; exact hRo.mul_mem hy' hx'
        inv_mem' := by
          rintro x ⟨hx, hx'⟩
          exact ⟨hx', by simpa using hx⟩ }
    have hle : unitGroup R ≤ U := by
      rw [unitGroup, Subgroup.closure_le]
      rintro v ⟨hv, v', hv', hvv', -⟩
      exact ⟨hv, by rwa [Units.inv_eq_of_mul_eq_one_right hvv']⟩
    obtain ⟨hwR, hwinv⟩ := hle hw
    have hwu : IsUnitOf R (w : ℍ[ℚ, a, b]) := ⟨hwR, _, hwinv, by simp, by simp⟩
    have hw0 : (w : ℍ[ℚ, a, b]) ≠ 0 := w.ne_zero
    have hdet : ((nrd (w : ℍ[ℚ, a, b]) : ℚ) : ℝ) = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.mp hker)
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this
      rw [← CerednikDrinfeld.det_map_eq_nrd ha hb ι hι]
      exact this
    refine ⟨w, hwu, by exact_mod_cast hdet, hw0, ?_⟩
    ext
    rw [toGL_val _ hw0]; rfl

  have hrep : ∀ ℓ : ℕ, ℓ.Prime → ∃ S : Finset ℍ[ℚ, a, b],
      (∀ x ∈ S, P ℓ x) ∧ (∀ y, P ℓ y → ∃! x, x ∈ S ∧ LRel R x y) := by
    intro ℓ hℓ
    obtain ⟨T, hTR, hT⟩ :=
      CerednikDrinfeld.exists_finset_forall_nrd_eq_exists_mul_unit hdiv R hRo (ℓ : ℚ)

    have hcover : ∀ y, P ℓ y → ∃ t ∈ T, LRel R (star t) y := by
      rintro y ⟨hyR, hyn, -⟩
      obtain ⟨t, htT, u, hu, hnu, hsy⟩ := hT (star y) (star_mem hRo hyR) (by rw [nrd_star, hyn])
      refine ⟨t, htT, star u, isUnitOf_star hRo hu, by rw [nrd_star, hnu], ?_⟩
      rw [← star_star y, hsy, star_mul]
    let cls : ℍ[ℚ, a, b] → Set ℍ[ℚ, a, b] := fun x => {z | LRel R x z}
    have cls_eq : ∀ x x', LRel R x x' → cls x = cls x' := by
      intro x x' h
      ext z
      exact ⟨fun hz => LRel.trans hRo h.symm hz, fun hz => LRel.trans hRo h hz⟩
    let rep : Set ℍ[ℚ, a, b] → ℍ[ℚ, a, b] := fun c =>
      if h : ∃ y, P ℓ y ∧ y ∈ c then h.choose else 0
    let I : Finset ℍ[ℚ, a, b] := T.filter fun t => ∃ y, P ℓ y ∧ LRel R (star t) y
    let S : Finset ℍ[ℚ, a, b] := (I.image fun t => cls (star t)).image rep
    have rep_spec : ∀ t ∈ I, P ℓ (rep (cls (star t))) ∧ LRel R (star t) (rep (cls (star t))) := by
      intro t ht
      have hex : ∃ y, P ℓ y ∧ y ∈ cls (star t) := by
        obtain ⟨-, y, hy, hty⟩ := Finset.mem_filter.mp ht
        exact ⟨y, hy, hty⟩
      have := hex.choose_spec
      simp only [rep, dif_pos hex]
      exact this
    refine ⟨S, ?_, ?_⟩
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hc
      exact (rep_spec t ht).1
    · intro y hy
      obtain ⟨t, htT, hty⟩ := hcover y hy
      have htI : t ∈ I := Finset.mem_filter.mpr ⟨htT, y, hy, hty⟩
      refine ⟨rep (cls (star t)), ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_image.mpr ⟨cls (star t), Finset.mem_image.mpr ⟨t, htI, rfl⟩, rfl⟩
      · exact LRel.trans hRo (rep_spec t htI).2.symm hty
      · rintro x ⟨hxS, hxy⟩
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hxS
        obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp hc
        have h1 : LRel R (star t') (star t) :=
          LRel.trans hRo (LRel.trans hRo (rep_spec t' ht').2 hxy) hty.symm
        rw [cls_eq _ _ h1]
  choose Sfun hSP hSuniq using hrep

  refine ⟨fun ℓ hℓ => (Sfun ℓ hℓ).val.map toGL, ?_, ?_⟩
  ·
    intro ℓ hℓ
    have hℓ0 : ((ℓ : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
    refine ⟨Sfun ℓ hℓ, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨hxR, hxn, hh⟩ := hSP ℓ hℓ x hx
      exact ⟨hxR, hxn, by simpa [h𝒮] using hh⟩
    · intro y hyR hyn hh
      have hPy : P ℓ y := ⟨hyR, hyn, by simpa [h𝒮] using hh⟩
      obtain ⟨x, ⟨hxS, u, hu, hnu, hux⟩, huniq⟩ := hSuniq ℓ hℓ y hPy
      refine ⟨x, ⟨hxS, u, hu, hnu, hux⟩, ?_⟩
      rintro x' ⟨hx'S, u', hu', hnu', hux'⟩
      exact huniq x' ⟨hx'S, u', hu', hnu', hux'⟩
    · simp only [Multiset.map_id', Multiset.pure_def]
      change Multiset.bind (Multiset.map toGL (Sfun ℓ hℓ).val)
          (fun g => ({((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)} : Multiset (Matrix (Fin 2) (Fin 2) ℝ))) = _
      rw [Multiset.bind_singleton, Multiset.map_map]
      refine Multiset.map_congr rfl fun x hx => ?_
      simp only [Function.comp_apply]
      have hx0 : x ≠ 0 := by
        rintro rfl
        have := (hSP ℓ hℓ 0 hx).2.1
        rw [nrd_zero] at this
        exact hℓ0 this.symm
      exact toGL_val x hx0
  ·
    intro ℓ hℓ γ hγ τ
    have hℓ0 : ((ℓ : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
    obtain ⟨u₀, hu₀, hnu₀, hu₀0, rfl⟩ := hΓ γ hγ
    set S := Sfun ℓ hℓ with hSdef
    have hS0 : ∀ x ∈ S, x ≠ 0 := by
      rintro x hx rfl
      have := (hSP ℓ hℓ 0 hx).2.1
      rw [nrd_zero] at this
      exact hℓ0 this.symm

    have hPmul : ∀ x, P ℓ x → P ℓ (x * u₀) := by
      rintro x ⟨hxR, hxn, h, hh, hhx⟩
      refine ⟨hRo.mul_mem hxR hu₀.1, by rw [QuaternionAlgebra.nrd_mul, hxn, hnu₀, mul_one], ?_⟩
      obtain ⟨h', hh', hh'val⟩ := hstab Λ R hΛo hRo hRΛ N ℓ hu₀ (by simpa [h𝒮] using hh)
      refine ⟨h', by simpa [h𝒮] using hh', ?_⟩
      rw [hh'val, hhx, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

    have hσex : ∀ x ∈ S, ∃! x', x' ∈ S ∧ LRel R x' (x * u₀) :=
      fun x hx => hSuniq ℓ hℓ (x * u₀) (hPmul x (hSP ℓ hℓ x hx))
    let σ : ∀ x ∈ S, ℍ[ℚ, a, b] := fun x hx => (hσex x hx).choose
    have hσS : ∀ x (hx : x ∈ S), σ x hx ∈ S := fun x hx => (hσex x hx).choose_spec.1.1
    have hσrel : ∀ x (hx : x ∈ S), LRel R (σ x hx) (x * u₀) := fun x hx => (hσex x hx).choose_spec.1.2
    have hσinj : ∀ x₁ (h₁ : x₁ ∈ S) x₂ (h₂ : x₂ ∈ S), σ x₁ h₁ = σ x₂ h₂ → x₁ = x₂ := by
      intro x₁ h₁ x₂ h₂ heq

      have h12 : LRel R (x₁ * u₀) (x₂ * u₀) :=
        LRel.trans hRo (hσrel x₁ h₁).symm (heq ▸ hσrel x₂ h₂)
      have h12' : LRel R x₁ x₂ := by
        obtain ⟨u, hu, hnu, hux⟩ := h12
        refine ⟨u, hu, hnu, ?_⟩
        have := congrArg (· * (hdiv u₀ hu₀0).unit⁻¹.val) hux
        simpa [mul_assoc, IsUnit.mul_val_inv] using this
      obtain ⟨x, -, huniq⟩ := hSuniq ℓ hℓ x₂ (hSP ℓ hℓ x₂ h₂)
      exact (huniq x₁ ⟨h₁, h12'⟩).trans (huniq x₂ ⟨h₂, LRel.refl hRo x₂⟩).symm
    have hσsurj : ∀ x' ∈ S, ∃ x hx, σ x hx = x' := by
      intro x' hx'
      obtain ⟨x, hx, h⟩ :=
        Finset.surj_on_of_inj_on_of_card_le σ hσS (fun a₁ a₂ h₁ h₂ => hσinj a₁ h₁ a₂ h₂) le_rfl x' hx'
      exact ⟨x, hx, h.symm⟩
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_eq_map_of_bij_of_nodup _ _ S.nodup S.nodup σ hσS hσinj hσsurj ?_
    intro x hx
    simp only [Function.comp_apply]
    obtain ⟨u', hu', hnu', hux'⟩ := hσrel x hx
    have hx0 := hS0 x hx
    have hσ0 := hS0 _ (hσS x hx)
    have hu'0 : u' ≠ 0 := by rintro rfl; simp at hnu'
    rw [← mul_smul, ← toGL_mul x u₀ hx0 hu₀0, ← hux', toGL_mul u' _ hu'0 hσ0, mul_smul]
    exact MulAction.orbit_smul (⟨toGL u', toGL_mem u' hu' hnu'⟩ : ↥(fuchsianGroup R ι)) _

end S_CerednikDrinfeld_exists_heckeFamily_map_orbit_eq_of_isEichlerOrder
end P2MW
export P2MW.S_CerednikDrinfeld_exists_heckeFamily_map_orbit_eq_of_isEichlerOrder (solution)
