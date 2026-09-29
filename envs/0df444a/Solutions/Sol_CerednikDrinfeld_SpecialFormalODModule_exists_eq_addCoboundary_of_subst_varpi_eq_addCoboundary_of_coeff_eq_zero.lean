-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_eq_addCoboundary_of_subst_varpi_eq_addCoboundary_of_coeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/1fd5b6f1-0353-51ed-b40f-0773c9b4884d

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient
import Theorems.Thm_MvFormalGroup_IsSymmTwoCocycle_addCoboundary_sum_subst_nthSeries_eq_and_exists_eq_addCoboundary_of_mem_span
import Theorems.Thm_CerednikDrinfeld_FormalODModule_connectingSum_smul_add_and_addCoboundary_and_subst_act_and_addCoboundary_eq_subst_nthSeries_and_mem_span
import Theorems.Thm_MvFormalGroup_mem_span_X_pow_of_addCoboundary_mem_span_of_coeff_single_eq_zero
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_span_range_varpi_eq_span_X_pow_of_linearPart_varpi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_eq_addCoboundary_of_subst_varpi_eq_addCoboundary_of_coeff_eq_zero
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero"

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace P2mOSC5b

universe u

theorem injective_of_existsUnique_expansion {A : Type*} [CommRing A] [NoZeroDivisors A]
    [Nontrivial A] (φ : A →+* A) {ι : Type*} [Fintype ι] (b : ι → A)
    (hb : ∀ x : A, ∃! c : ι → A, x = ∑ i, φ (c i) * b i) :
    Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨c₁, hc₁, huniq⟩ := hb 1
  have hc₁' : (1 : A) = ∑ i, φ (c₁ i + c * c₁ i) * b i := by
    refine hc₁.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_add, map_mul, hc, zero_mul, add_zero]
  have hcc : (fun i => c₁ i + c * c₁ i) = c₁ := huniq _ hc₁'
  by_contra hne
  have hzero : ∀ i, c₁ i = 0 := fun i => by
    have hi := congrFun hcc i
    have hmul : c * c₁ i = 0 := by
      have := congrArg (fun t => t - c₁ i) hi
      simpa using this
    exact (mul_eq_zero.mp hmul).resolve_left hne
  have : (1 : A) = 0 := by
    rw [hc₁]
    exact Finset.sum_eq_zero fun i _ => by rw [hzero i, map_zero, zero_mul]
  exact one_ne_zero this

theorem subst_injective_of_finite_quotient {k : Type u} [Field k] {d : ℕ}
    (g : Fin d → MvPowerSeries (Fin d) k) (hg : ∀ i, constantCoeff (g i) = 0)
    (hfin : Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g))) :
    Function.Injective (subst g : MvPowerSeries (Fin d) k → MvPowerSeries (Fin d) k) := by
  obtain ⟨-, -, b, hb⟩ := MvPowerSeries.finite_flat_exists_basis_substAlgHom_of_finite_quotient g hg hfin
  have hinj := injective_of_existsUnique_expansion
    (substAlgHom (R := k) (hasSubst_of_constantCoeff_zero hg)).toRingHom b (fun x => by
      simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_substAlgHom] using hb x)
  intro x y hxy
  apply hinj
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_substAlgHom]
  exact hxy

theorem subst_mem_span {R : Type*} [CommRing R] {σ : Type*} [Fintype σ] [DecidableEq σ] {τ : Type*}
    (a : σ → MvPowerSeries τ R) (ha : ∀ s, (a s).constantCoeff = 0)
    (f : MvPowerSeries σ R) (hf : f.constantCoeff = 0) :
    subst a f ∈ Ideal.span (Set.range a) := by
  classical
  have hsa : HasSubst a := hasSubst_of_constantCoeff_zero ha

  have hpeel : ∃ q : σ → MvPowerSeries σ R, f = ∑ s, X s * q s := by
    suffices h : ∀ (T : Finset σ) (f : MvPowerSeries σ R),
        (∀ d : σ →₀ ℕ, (∀ s ∈ T, d s = 0) → coeff d f = 0) →
        ∃ q : σ → MvPowerSeries σ R, f = ∑ s ∈ T, X s * q s by
      exact h Finset.univ f (fun d hd => by
        have : d = 0 := Finsupp.ext fun s => hd s (Finset.mem_univ s)
        rw [this, coeff_zero_eq_constantCoeff_apply, hf])
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro f hf
      refine ⟨fun _ => 0, ?_⟩
      rw [Finset.sum_empty]
      ext d
      rw [map_zero]
      exact hf d (fun s hs => absurd hs (Finset.notMem_empty s))
    | @insert s T hs ih =>
      intro f hf
      let f₀ : MvPowerSeries σ R := fun d => if d s = 0 then coeff d f else 0
      have hf₀ : ∀ d, coeff d f₀ = if d s = 0 then coeff d f else 0 := fun d => rfl
      have hdvd : (X s : MvPowerSeries σ R) ∣ f - f₀ := by
        rw [X_dvd_iff]
        intro d hd
        rw [map_sub, hf₀, if_pos hd, sub_self]
      obtain ⟨q', hq'⟩ := hdvd
      obtain ⟨q, hq⟩ := ih f₀ (by
        intro d hd
        rw [hf₀]
        split_ifs with hds
        · exact hf d (fun t ht => by
            rcases Finset.mem_insert.mp ht with rfl | ht
            · exact hds
            · exact hd t ht)
        · rfl)
      refine ⟨Function.update q s q', ?_⟩
      rw [Finset.sum_insert hs, Function.update_self]
      have hrest : ∑ t ∈ T, X t * Function.update q s q' t = ∑ t ∈ T, X t * q t := by
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [Function.update_of_ne (ne_of_mem_of_not_mem ht hs)]
      rw [hrest, ← hq, ← hq']
      ring
  obtain ⟨qq, hqq⟩ := hpeel
  rw [hqq, ← coe_substAlgHom hsa, map_sum]
  refine Ideal.sum_mem _ fun s _ => ?_
  rw [map_mul, substAlgHom_X]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s, rfl⟩)

end P2mOSC5b

universe u

open P2mOSC5b CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hnode₀ : ∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)
    (hnode₁ : ∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)
    (γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k) (hγ : X₀.F.IsSymmTwoCocycle γ)
    (g : MvPowerSeries (Fin 2) k) (hg0 : MvPowerSeries.constantCoeff g = 0)
    (hglin : ∀ m, MvPowerSeries.coeff (Finsupp.single m 1) g = 0) :
    let pull : (Fin 2 → MvPowerSeries (Fin 2) k) → MvPowerSeries (Fin 2 ⊕ Fin 2) k →
        MvPowerSeries (Fin 2 ⊕ Fin 2) k := fun φ Γ =>
      MvPowerSeries.subst
        (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
          fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
        Γ
    pull X₀.varpi γ = X₀.F.addCoboundary g →
    ∃ b : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff b = 0 ∧ γ = X₀.F.addCoboundary b := by
  intro pull hpull
  classical
  haveI := X₀.isComm
  have hϖ0 : ∀ i, constantCoeff (X₀.varpi i) = 0 := X₀.isLawHom_varpi.1
  have hsϖ : HasSubst X₀.varpi := hasSubst_of_constantCoeff_zero hϖ0

  obtain ⟨-, hΘcob, -, hΘϖ, -, hpeel⟩ :=
    CerednikDrinfeld.FormalODModule.connectingSum_smul_add_and_addCoboundary_and_subst_act_and_addCoboundary_eq_subst_nthSeries_and_mem_span
      X₀.toFormalODModule

  have hnode := CerednikDrinfeld.SpecialFormalODModule.span_range_varpi_eq_span_X_pow_of_linearPart_varpi
    X₀ hnode₀ hnode₁
  have hJ : Ideal.span (Set.range (Sum.elim
      (fun i => MvPowerSeries.subst
        (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi i))
      (fun i => MvPowerSeries.subst
        (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi i)))) ≤
      Ideal.span (Set.range fun s : Fin 2 ⊕ Fin 2 => (MvPowerSeries.X s : MvPowerSeries (Fin 2 ⊕ Fin 2) k) ^ q) := by
    apply Ideal.span_le.mpr
    have hXL : HasSubst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    have hXR : HasSubst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    have key : ∀ (e : Fin 2 → Fin 2 ⊕ Fin 2) (he : HasSubst (fun l => (MvPowerSeries.X (e l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k))) (i : Fin 2),
        MvPowerSeries.subst (fun l => (MvPowerSeries.X (e l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi i) ∈
        Ideal.span (Set.range fun s : Fin 2 ⊕ Fin 2 => (MvPowerSeries.X s : MvPowerSeries (Fin 2 ⊕ Fin 2) k) ^ q) := by
      intro e he i
      have hmem : X₀.varpi i ∈ Ideal.span (Set.range fun j : Fin 2 => (MvPowerSeries.X j : MvPowerSeries (Fin 2) k) ^ q) := by
        rw [← hnode]
        exact Ideal.subset_span ⟨i, rfl⟩
      have := Ideal.mem_map_of_mem (substAlgHom he).toRingHom hmem
      rw [Ideal.map_span] at this
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_substAlgHom] at this
      refine Ideal.span_mono ?_ this
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      refine ⟨e j, ?_⟩
      show X (e j) ^ q = subst _ (X j ^ q)
      rw [← coe_substAlgHom he, map_pow, substAlgHom_X]
    rintro _ ⟨s, rfl⟩
    rcases s with i | i
    · exact key Sum.inl hXL i
    · exact key Sum.inr hXR i
  have hcob : X₀.F.addCoboundary g ∈
      Ideal.span (Set.range fun s : Fin 2 ⊕ Fin 2 => (MvPowerSeries.X s : MvPowerSeries (Fin 2 ⊕ Fin 2) k) ^ q) := by
    rw [← hpull]
    exact hJ (hpeel X₀.varpi γ hϖ0 hγ.constantCoeff_eq_zero)

  have hg : g ∈ Ideal.span (Set.range X₀.varpi) := by
    rw [hnode]
    exact MvFormalGroup.mem_span_X_pow_of_addCoboundary_mem_span_of_coeff_single_eq_zero q X₀.F g hg0 hglin hcob

  have hq : X₀.F.nthSeries q = X₀.varpi.comp X₀.varpi := by
    rw [X₀.varpi_comp_varpi, X₀.act_natCast]
  have hcomp : MvPowerSeries.subst (X₀.F.nthSeries q) g = MvPowerSeries.subst X₀.varpi (MvPowerSeries.subst X₀.varpi g) := by
    rw [hq, subst_comp_subst_apply hsϖ hsϖ]
    rfl
  have hΘeq : MvPowerSeries.subst X₀.varpi
      (∑ i ∈ Finset.range q, MvPowerSeries.subst (Sum.elim (X₀.F.nthSeries i) fun l => MvPowerSeries.X l) γ) =
      MvPowerSeries.subst X₀.varpi (MvPowerSeries.subst X₀.varpi g) := by
    rw [← hcomp, ← hΘcob g hg0, ← hpull]
    exact (hΘϖ γ).symm

  have hfinq : Module.Finite k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range (X₀.F.nthSeries q))) := by
    have h := X₀.hasHeight.1
    rwa [X₀.act_natCast] at h
  have hle : Ideal.span (Set.range (X₀.F.nthSeries q)) ≤ Ideal.span (Set.range X₀.varpi) := by
    rw [hq]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact subst_mem_span X₀.varpi hϖ0 (X₀.varpi i) (hϖ0 i)
  have hfinϖ : Module.Finite k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range X₀.varpi)) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ k hle).toLinearMap (Ideal.Quotient.factor_surjective hle)
  have hinj := subst_injective_of_finite_quotient X₀.varpi hϖ0 hfinϖ
  have hΘ : (∑ i ∈ Finset.range q, MvPowerSeries.subst (Sum.elim (X₀.F.nthSeries i) fun l => MvPowerSeries.X l) γ) =
      MvPowerSeries.subst X₀.varpi g := hinj hΘeq

  have hΘmem : (∑ i ∈ Finset.range q, MvPowerSeries.subst (Sum.elim (X₀.F.nthSeries i) fun l => MvPowerSeries.X l) γ) ∈
      Ideal.span (Set.range (X₀.F.nthSeries q)) := by
    rw [hΘ, hq]
    have := Ideal.mem_map_of_mem (substAlgHom hsϖ).toRingHom hg
    rw [Ideal.map_span] at this
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_substAlgHom] at this
    refine Ideal.span_mono ?_ this
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, rfl⟩

  have hh : Module.finrank k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range (X₀.F.nthSeries q))) = q ^ 4 := by
    have h := X₀.hasHeight.2.2 k (RingHom.id k)
    rw [X₀.act_natCast] at h
    have hid : Series.map (RingHom.id k) (X₀.F.nthSeries q) = X₀.F.nthSeries q := by
      funext i
      show MvPowerSeries.map (RingHom.id k) _ = _
      rw [MvPowerSeries.map_id]
      rfl
    rwa [hid] at h
  obtain ⟨b, hb0, hb⟩ :=
    (MvFormalGroup.IsSymmTwoCocycle.addCoboundary_sum_subst_nthSeries_eq_and_exists_eq_addCoboundary_of_mem_span
      q 4 hh hγ).2 hΘmem
  exact ⟨b, hb0, hb⟩

end
end S_CerednikDrinfeld_SpecialFormalODModule_exists_eq_addCoboundary_of_subst_varpi_eq_addCoboundary_of_coeff_eq_zero
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_eq_addCoboundary_of_subst_varpi_eq_addCoboundary_of_coeff_eq_zero (solution)
