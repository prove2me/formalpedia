-- Prove2me | solution 1 for Coalgebra.exists_finiteDimensional_le_comul_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/58cd92ca-3af4-5bef-8571-b974408d941b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Coalgebra_exists_finiteDimensional_le_comul_mem_span

set_option autoImplicit false

open scoped TensorProduct

universe u v

namespace S17Tb0

variable {k : Type u} [Field k] {C : Type v} [AddCommGroup C] [Module k C]

noncomputable def cR (ψ : Module.Dual k C) : C ⊗[k] C →ₗ[k] C :=
  (TensorProduct.rid k C).toLinearMap ∘ₗ LinearMap.lTensor C ψ

@[scoped simp] theorem cR_tmul (ψ : Module.Dual k C) (a b : C) : cR ψ (a ⊗ₜ[k] b) = ψ b • a := by
  simp [cR]

noncomputable def cL (φ : Module.Dual k C) : C ⊗[k] C →ₗ[k] C :=
  (TensorProduct.lid k C).toLinearMap ∘ₗ LinearMap.rTensor C φ

@[scoped simp] theorem cL_tmul (φ : Module.Dual k C) (a b : C) : cL φ (a ⊗ₜ[k] b) = φ a • b := by
  simp [cL]

theorem lTensor_cR_assoc (ψ : Module.Dual k C) (z : C ⊗[k] C) (r : C) :
    LinearMap.lTensor C (cR ψ) (TensorProduct.assoc k C C C (z ⊗ₜ[k] r)) = ψ r • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul p q => simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  | add z₁ z₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add, h₁, h₂, smul_add]

theorem rTensor_cL_assoc_symm (φ : Module.Dual k C) (p : C) (z : C ⊗[k] C) :
    LinearMap.rTensor C (cL φ) ((TensorProduct.assoc k C C C).symm (p ⊗ₜ[k] z)) = φ p • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul q r => simp [TensorProduct.smul_tmul']
  | add z₁ z₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂, smul_add]

theorem exists_dual_family {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → C) (he : LinearIndependent k e) :
    ∃ ψ : ι → Module.Dual k C, ∀ i j, ψ i (e j) = if i = j then 1 else 0 := by
  classical
  let b := Module.Basis.span he
  have hb : ∀ j, (b j : C) = e j := fun j => congrArg Subtype.val (Module.Basis.span_apply he j)

  have hext : ∀ i, ∃ g : C →ₗ[k] k, g ∘ₗ (Submodule.span k (Set.range e)).subtype = b.coord i := fun i =>
    LinearMap.exists_extend (b.coord i)
  choose ψ hψ using hext
  refine ⟨ψ, fun i j => ?_⟩
  have : ψ i (b j : C) = b.coord i (b j) := by
    rw [← hψ i]; rfl
  rw [← hb, this, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp [eq_comm]

theorem eq_sum_cR_tmul {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → C) (ψ : ι → Module.Dual k C)
    (hψ : ∀ i j, ψ i (e j) = if i = j then 1 else 0)
    (A : Submodule k C) (t : C ⊗[k] C)
    (ht : t ∈ Submodule.span k {s : C ⊗[k] C | ∃ a ∈ A, ∃ b ∈ Submodule.span k (Set.range e), s = a ⊗ₜ[k] b}) :
    t = ∑ l, cR (ψ l) t ⊗ₜ[k] e l := by
  induction ht using Submodule.span_induction with
  | mem s hs =>
      obtain ⟨a, -, b, hb, rfl⟩ := hs

      have hbexp : b = ∑ l, ψ l b • e l := by
        induction hb using Submodule.span_induction with
        | mem c hc =>
            obtain ⟨j, rfl⟩ := hc
            rw [Finset.sum_eq_single j]
            · rw [hψ, if_pos rfl, one_smul]
            · intro l _ hlj; rw [hψ, if_neg hlj, zero_smul]
            · intro h; exact absurd (Finset.mem_univ j) h
        | zero => simp
        | add c d _ _ hc hd =>
            conv_lhs => rw [hc, hd]
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [map_add, add_smul]
        | smul r c _ hc =>
            conv_lhs => rw [hc]
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [map_smul, smul_eq_mul, mul_smul]
      conv_lhs => rw [hbexp]
      rw [TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [cR_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | zero => simp
  | add s t _ _ hs ht =>
      conv_lhs => rw [hs, ht]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_add, TensorProduct.add_tmul]
  | smul r s _ hs =>
      conv_lhs => rw [hs]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, TensorProduct.smul_tmul']

theorem eq_sum_tmul_cL {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → C) (φ : ι → Module.Dual k C)
    (hφ : ∀ i j, φ i (u j) = if i = j then 1 else 0)
    (B : Submodule k C) (t : C ⊗[k] C)
    (ht : t ∈ Submodule.span k {s : C ⊗[k] C | ∃ a ∈ Submodule.span k (Set.range u), ∃ b ∈ B, s = a ⊗ₜ[k] b}) :
    t = ∑ j, u j ⊗ₜ[k] cL (φ j) t := by
  induction ht using Submodule.span_induction with
  | mem s hs =>
      obtain ⟨a, ha, b, -, rfl⟩ := hs
      have haexp : a = ∑ j, φ j a • u j := by
        induction ha using Submodule.span_induction with
        | mem c hc =>
            obtain ⟨j, rfl⟩ := hc
            rw [Finset.sum_eq_single j]
            · rw [hφ, if_pos rfl, one_smul]
            · intro l _ hlj; rw [hφ, if_neg hlj, zero_smul]
            · intro h; exact absurd (Finset.mem_univ j) h
        | zero => simp
        | add c d _ _ hc hd =>
            conv_lhs => rw [hc, hd]
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [map_add, add_smul]
        | smul r c _ hc =>
            conv_lhs => rw [hc]
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [map_smul, smul_eq_mul, mul_smul]
      conv_lhs => rw [haexp]
      rw [TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [cL_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | zero => simp
  | add s t _ _ hs ht =>
      conv_lhs => rw [hs, ht]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_add, TensorProduct.tmul_add]
  | smul r s _ hs =>
      conv_lhs => rw [hs]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, TensorProduct.tmul_smul]

theorem cR_mem (ψ : Module.Dual k C) (A B : Submodule k C) (t : C ⊗[k] C)
    (ht : t ∈ Submodule.span k {s : C ⊗[k] C | ∃ a ∈ A, ∃ b ∈ B, s = a ⊗ₜ[k] b}) : cR ψ t ∈ A := by
  induction ht using Submodule.span_induction with
  | mem s hs => obtain ⟨a, ha, b, -, rfl⟩ := hs; rw [cR_tmul]; exact A.smul_mem _ ha
  | zero => simp
  | add s t _ _ hs ht => rw [map_add]; exact A.add_mem hs ht
  | smul r s _ hs => rw [map_smul]; exact A.smul_mem _ hs

theorem cL_mem (φ : Module.Dual k C) (A B : Submodule k C) (t : C ⊗[k] C)
    (ht : t ∈ Submodule.span k {s : C ⊗[k] C | ∃ a ∈ A, ∃ b ∈ B, s = a ⊗ₜ[k] b}) : cL φ t ∈ B := by
  induction ht using Submodule.span_induction with
  | mem s hs => obtain ⟨a, -, b, hb, rfl⟩ := hs; rw [cL_tmul]; exact B.smul_mem _ hb
  | zero => simp
  | add s t _ _ hs ht => rw [map_add]; exact B.add_mem hs ht
  | smul r s _ hs => rw [map_smul]; exact B.smul_mem _ hs

theorem span_tmul_mono {A A' B B' : Submodule k C} (hA : A ≤ A') (hB : B ≤ B') :
    Submodule.span k {s : C ⊗[k] C | ∃ a ∈ A, ∃ b ∈ B, s = a ⊗ₜ[k] b}
      ≤ Submodule.span k {s : C ⊗[k] C | ∃ a ∈ A', ∃ b ∈ B', s = a ⊗ₜ[k] b} :=
  Submodule.span_mono fun s ⟨a, ha, b, hb, hs⟩ => ⟨a, hA ha, b, hB hb, hs⟩

theorem tmul_mem_span {A B : Submodule k C} {a b : C} (ha : a ∈ A) (hb : b ∈ B) :
    a ⊗ₜ[k] b ∈ Submodule.span k {s : C ⊗[k] C | ∃ a ∈ A, ∃ b ∈ B, s = a ⊗ₜ[k] b} :=
  Submodule.subset_span ⟨a, ha, b, hb, rfl⟩

end S17Tb0
p2m_reactivate "P2MW.S_Coalgebra_exists_finiteDimensional_le_comul_mem_span.S17Tb0"

open S17Tb0 in
theorem solution
    {k : Type u} [Field k] {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
    (K : Submodule k C)
    (hK : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : C ⊗[k] C | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (x : C) (hx : x ∈ K) :
    ∃ D : Submodule k C, D ≤ K ∧ FiniteDimensional k ↥D ∧ x ∈ D ∧
      ∀ y ∈ D, Coalgebra.comul (R := k) y ∈
        Submodule.span k {t : C ⊗[k] C | ∃ a ∈ D, ∃ b ∈ D, t = a ⊗ₜ[k] b} := by
  classical
  obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.mp (hK x hx)
  choose a ha b hb hab using (fun i => (g i).2)

  obtain ⟨t, ht_sub, ht_span, ht_li⟩ := exists_linearIndependent k (Set.range b)
  have ht_fin : t.Finite := (Set.finite_range b).subset ht_sub
  haveI : Fintype ↥t := ht_fin.fintype
  let e : ↥t → C := Subtype.val
  obtain ⟨ψ, hψ⟩ := exists_dual_family e ht_li
  have hrange_e : Set.range e = t := Subtype.range_coe
  have hb_mem : ∀ i, b i ∈ Submodule.span k (Set.range e) := fun i => by
    rw [hrange_e, ht_span]; exact Submodule.subset_span ⟨i, rfl⟩
  have he_mem_K : ∀ l, e l ∈ K := fun l => by
    have : e l ∈ Submodule.span k (Set.range b) := by
      rw [← ht_span]; exact Submodule.subset_span (hrange_e ▸ ⟨l, rfl⟩)
    exact (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hb i)) this
  have hΔx : Coalgebra.comul (R := k) x ∈
      Submodule.span k {s : C ⊗[k] C | ∃ a ∈ K, ∃ b ∈ Submodule.span k (Set.range e), s = a ⊗ₜ[k] b} := by
    rw [← hsum]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    rw [hab i]
    exact tmul_mem_span (ha i) (hb_mem i)

  let a' : ↥t → C := fun l => cR (ψ l) (Coalgebra.comul (R := k) x)
  have ha'K : ∀ l, a' l ∈ K := fun l => cR_mem (ψ l) K _ _ hΔx
  have hdag : Coalgebra.comul (R := k) x = ∑ l, a' l ⊗ₜ[k] e l := eq_sum_cR_tmul e ψ hψ K _ hΔx

  have hx_eq : x = ∑ l, Coalgebra.counit (R := k) (e l) • a' l := by
    have h1 : (TensorProduct.rid k C) (LinearMap.lTensor C (Coalgebra.counit (R := k) (A := C))
        (Coalgebra.comul (R := k) x)) = x := by
      rw [Coalgebra.lTensor_counit_comul]; simp
    rw [hdag, map_sum, map_sum] at h1
    simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul] at h1
    exact h1.symm

  have hΔe : ∀ l, Coalgebra.comul (R := k) (e l) ∈
      Submodule.span k {s : C ⊗[k] C | ∃ a ∈ K, ∃ b ∈ K, s = a ⊗ₜ[k] b} := fun l => hK _ (he_mem_K l)
  let w : ↥t → ↥t → C := fun l m => cR (ψ m) (Coalgebra.comul (R := k) (e l))
  have hwK : ∀ l m, w l m ∈ K := fun l m => cR_mem _ K K _ (hΔe l)
  have hΔa' : ∀ m, Coalgebra.comul (R := k) (a' m) = ∑ l, a' l ⊗ₜ[k] w l m := by
    intro m
    have hco := Coalgebra.coassoc_apply (R := k) x
    have h2 := congrArg (LinearMap.lTensor C (cR (ψ m))) hco
    rw [hdag] at h2
    simp only [map_sum] at h2
    simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, lTensor_cR_assoc, hψ, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h2
    exact h2
  let N : Submodule k C := Submodule.span k (Set.range a')
  have hNK : N ≤ K := Submodule.span_le.mpr (by rintro _ ⟨l, rfl⟩; exact ha'K l)
  have hxN : x ∈ N := by
    rw [hx_eq]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  have hΔN : ∀ y ∈ N, Coalgebra.comul (R := k) y ∈
      Submodule.span k {s : C ⊗[k] C | ∃ a ∈ N, ∃ b ∈ K, s = a ⊗ₜ[k] b} := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨m, rfl⟩ := hz
        rw [hΔa' m]
        exact Submodule.sum_mem _ fun l _ => tmul_mem_span (Submodule.subset_span ⟨l, rfl⟩) (hwK l m)
    | zero => simp
    | add _ _ _ _ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
    | smul r _ _ h => rw [map_smul]; exact Submodule.smul_mem _ _ h

  obtain ⟨t', ht'_sub, ht'_span, ht'_li⟩ := exists_linearIndependent k (Set.range a')
  haveI : Fintype ↥t' := ((Set.finite_range a').subset ht'_sub).fintype
  let u : ↥t' → C := Subtype.val
  obtain ⟨φ, hφ⟩ := exists_dual_family u ht'_li
  have hspan_u : Submodule.span k (Set.range u) = N := by
    show Submodule.span k (Set.range (Subtype.val : ↥t' → C)) = N
    rw [Subtype.range_coe]; exact ht'_span
  have hu_N : ∀ j, u j ∈ N := fun j => by rw [← hspan_u]; exact Submodule.subset_span ⟨j, rfl⟩
  let v : ↥t' → ↥t' → C := fun j m => cL (φ j) (Coalgebra.comul (R := k) (u m))
  have hvK : ∀ j m, v j m ∈ K := fun j m => cL_mem _ N K _ (hΔN _ (hu_N m))
  have hddag : ∀ m, Coalgebra.comul (R := k) (u m) = ∑ j, u j ⊗ₜ[k] v j m := by
    intro m
    apply eq_sum_tmul_cL u φ hφ K
    rw [hspan_u]
    exact hΔN _ (hu_N m)

  let D : Submodule k C := Submodule.span k (Set.range fun jm : ↥t' × ↥t' => v jm.1 jm.2)
  have hvD : ∀ j m, v j m ∈ D := fun j m => Submodule.subset_span ⟨(j, m), rfl⟩
  have hu_eq : ∀ m, u m = ∑ j, Coalgebra.counit (R := k) (u j) • v j m := by
    intro m
    have h1 : (TensorProduct.lid k C) (LinearMap.rTensor C (Coalgebra.counit (R := k) (A := C))
        (Coalgebra.comul (R := k) (u m))) = u m := by
      rw [Coalgebra.rTensor_counit_comul]; simp
    rw [hddag, map_sum, map_sum] at h1
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul] at h1
    exact h1.symm
  have huD : ∀ m, u m ∈ D := fun m => by
    rw [hu_eq]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvD j m)
  have hND : N ≤ D := by
    rw [← hspan_u]
    exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact huD j)
  have hΔv : ∀ l m, Coalgebra.comul (R := k) (v l m) = ∑ j, v l j ⊗ₜ[k] v j m := by
    intro l m
    have hco := Coalgebra.coassoc_apply (R := k) (u m)
    have h2 : LinearMap.rTensor C (cL (φ l))
        (LinearMap.rTensor C (Coalgebra.comul (R := k)) (Coalgebra.comul (R := k) (u m)))
        = ∑ j, v l j ⊗ₜ[k] v j m := by
      rw [hddag, map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, hddag j, map_sum]
      simp only [cL_tmul, hφ, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have h3 : LinearMap.rTensor C (cL (φ l)) ((TensorProduct.assoc k C C C).symm
        (LinearMap.lTensor C (Coalgebra.comul (R := k)) (Coalgebra.comul (R := k) (u m))))
        = Coalgebra.comul (R := k) (v l m) := by
      rw [hddag, map_sum, map_sum, map_sum]
      simp only [LinearMap.lTensor_tmul, rTensor_cL_assoc_symm, hφ, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← hco, LinearEquiv.symm_apply_apply] at h3
    rw [← h3, h2]
  refine ⟨D, ?_, ?_, hND hxN, ?_⟩
  · exact Submodule.span_le.mpr (by rintro _ ⟨⟨j, m⟩, rfl⟩; exact hvK j m)
  · exact FiniteDimensional.span_of_finite k (Set.finite_range _)
  · intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨⟨l, m⟩, rfl⟩ := hz
        show Coalgebra.comul (R := k) (v l m) ∈ _
        rw [hΔv l m]
        exact Submodule.sum_mem _ fun j _ => tmul_mem_span (hvD l j) (hvD j m)
    | zero => simp
    | add _ _ _ _ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
    | smul r _ _ h => rw [map_smul]; exact Submodule.smul_mem _ _ h

end S_Coalgebra_exists_finiteDimensional_le_comul_mem_span
end P2MW
export P2MW.S_Coalgebra_exists_finiteDimensional_le_comul_mem_span (solution)
