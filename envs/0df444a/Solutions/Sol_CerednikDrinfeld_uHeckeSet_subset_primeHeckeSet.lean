-- Prove2me | solution 1 for CerednikDrinfeld.uHeckeSet_subset_primeHeckeSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/7e4d7f54-2aba-53d1-a35f-9399ad54b93a

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_Submodule_finiteAdeleBox_conjByFiniteIdele
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_uHeckeSet_subset_primeHeckeSet

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

namespace Ws43C1

variable {a b : ℚ}

open scoped Pointwise

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

noncomputable def cj (g : (ℍ𝔸)ˣ) : ℍ𝔸 →+ ℍ𝔸 :=
  (AddMonoidHom.mulRight ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)).comp (AddMonoidHom.mulLeft (g : ℍ𝔸))

theorem cj_apply (g : (ℍ𝔸)ˣ) (x : ℍ𝔸) : cj g x = (g : ℍ𝔸) * x * ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := rfl

theorem cj_mul (g g' : (ℍ𝔸)ˣ) : (cj g).comp (cj g') = cj (g * g') := by
  ext x
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, cj_apply, mul_inv_rev, Units.val_mul, mul_assoc]

theorem cj_inv_comp (g : (ℍ𝔸)ˣ) : (cj g⁻¹).comp (cj g) = AddMonoidHom.id _ := by
  rw [cj_mul, inv_mul_cancel]
  ext x
  simp [cj_apply]

theorem mem_conj_iff (Λ : Submodule ℤ ℍ[ℚ, a, b]) (g : (ℍ𝔸)ˣ) (z : ℍ[ℚ, a, b]) :
    z ∈ Submodule.conjByFiniteIdele Λ g ↔
      z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ (Submodule.finiteAdeleBox Λ).map (cj g) :=
  Submodule.mem_conjByFiniteIdele_iff Λ g z

theorem box_conj {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) (g : (ℍ𝔸)ˣ) :
    Submodule.finiteAdeleBox (Submodule.conjByFiniteIdele R g) = (Submodule.finiteAdeleBox R).map (cj g) :=
  Submodule.finiteAdeleBox_conjByFiniteIdele R hR.fg hR.spanTop g

theorem map_cj_box_eq_of_mem_stabilizer {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    {u : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer R) :
    (Submodule.finiteAdeleBox R).map (cj u) = Submodule.finiteAdeleBox R := by
  obtain ⟨hu1, hu2⟩ := (mem_stabilizer_iff hR u).mp hu
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [cj_apply]
    exact box_mul_mem hR (box_mul_mem hR hu1 hx) hu2
  · intro x hx
    refine ⟨cj u⁻¹ x, ?_, ?_⟩
    · rw [cj_apply, inv_inv]
      exact box_mul_mem hR (box_mul_mem hR hu2 hx) hu1
    · have := congrArg (fun f => f x) (cj_inv_comp u⁻¹)
      simpa only [inv_inv, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.id_apply] using this

theorem conj_eq_conj_of_unit {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    (n h u : (ℍ𝔸)ˣ) (hu : u ∈ Submodule.finiteIdeleStabilizer R) (hcj : cj u = cj h)
    (hc2 : Submodule.conjByFiniteIdele (Submodule.conjByFiniteIdele R n) h = R) :
    Submodule.conjByFiniteIdele R h = Submodule.conjByFiniteIdele R n := by

  have hbox_n := box_conj hR n
  have hRhn : R = Submodule.conjByFiniteIdele R (h * n) := by
    ext z
    rw [mem_conj_iff, ← cj_mul, ← AddSubgroup.map_map, ← hbox_n, ← mem_conj_iff, hc2]
  have E1 : Submodule.finiteAdeleBox R = ((Submodule.finiteAdeleBox R).map (cj n)).map (cj h) := by
    conv_lhs => rw [hRhn]
    rw [box_conj hR (h * n), ← cj_mul, AddSubgroup.map_map]

  have E2 : (Submodule.finiteAdeleBox R).map (cj n) = Submodule.finiteAdeleBox R := by
    have := congrArg (fun S => S.map (cj u⁻¹)) E1
    simp only [AddSubgroup.map_map] at this
    rw [← hcj, ← AddMonoidHom.comp_assoc, cj_inv_comp, AddMonoidHom.id_comp,
      map_cj_box_eq_of_mem_stabilizer hR (inv_mem hu)] at this
    exact this.symm
  have E3 : (Submodule.finiteAdeleBox R).map (cj h) = Submodule.finiteAdeleBox R := by
    rw [← hcj]; exact map_cj_box_eq_of_mem_stabilizer hR hu
  ext z
  rw [mem_conj_iff, mem_conj_iff, E2, E3]

end Ws43C1

open Ws43C1 in

theorem solution
    {a b : ℚ} (R : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ} (q : ℕ) [Fact q.Prime]
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hR : IsEichlerOrder R N) (hn : IsEichlerOrder (meetOrder R n) (N * q)) :
    uHeckeSet R n q ⊆ primeHeckeSet R q := by
  have hRo : QuaternionAlgebra.IsOrder R := hR.isOrder
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  intro h hh
  obtain ⟨⟨h1, h2, h3, h4⟩, hc2, hc3⟩ := hh
  have hSR : Submodule.finiteAdeleBox (meetOrder R n) ≤ Submodule.finiteAdeleBox R :=
    box_mono (inf_le_left : meetOrder R n ≤ R)
  refine ⟨hSR h1, hSR h2, ?_, ?_⟩
  ·
    intro hinv
    apply hc3
    exact conj_eq_conj_of_unit hRo n h h ((mem_stabilizer_iff hRo h).mpr ⟨hSR h1, hinv⟩) rfl hc2
  ·
    intro hmem
    apply hc3
    let u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
      ⟨(q : ℚ)⁻¹ • (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ),
        (q : ℚ) • ((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ),
        by rw [smul_mul_smul_comm, inv_mul_cancel₀ hq0, one_smul, Units.mul_inv],
        by rw [smul_mul_smul_comm, mul_inv_cancel₀ hq0, one_smul, Units.inv_mul]⟩
    have hu : u ∈ Submodule.finiteIdeleStabilizer R := (mem_stabilizer_iff hRo u).mpr ⟨hmem, hSR h2⟩
    refine conj_eq_conj_of_unit hRo n h u hu ?_ hc2
    ext x
    show ((q : ℚ)⁻¹ • (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) * x *
        ((q : ℚ) • ((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) =
      (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * x *
        ((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)
    rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ hq0, one_smul]

end S_CerednikDrinfeld_uHeckeSet_subset_primeHeckeSet
end P2MW
export P2MW.S_CerednikDrinfeld_uHeckeSet_subset_primeHeckeSet (solution)
