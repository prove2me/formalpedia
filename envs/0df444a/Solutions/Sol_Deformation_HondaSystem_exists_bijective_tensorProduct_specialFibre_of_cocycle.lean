-- Prove2me | solution 1 for Deformation.HondaSystem.exists_bijective_tensorProduct_specialFibre_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/43b4b330-c232-5016-ba67-5591d4aeef8d

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_Dieudonne_UnipotentWittCovector
import Definitions.Def_Dieudonne_FontaineFunctor
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_Deformation_SplitCoordinates
import Theorems.Thm_IsAdicComplete_of_module_finite_free_span_natCast
import Theorems.Thm_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle

set_option autoImplicit false

open scoped TensorProduct
p2m_open "MvPowerSeries P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.MvPowerSeries"

universe u v

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

namespace MvFormalGroup
p2m_export "MvFormalGroup" "IsComm map nthSeries nthSeries_zero nthSeries_succ mk toPowerSeries constantCoeff_eq_zero constantCoeff_nthSeries adicEval adicEval_mem_radical map_adicEval Points Points.val_zero Points.val_add Points.add_zero algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical"
p2m_open "MvFormalGroup"

variable {g : ℕ} {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

theorem toPowerSeries_injective :
    Function.Injective (MvFormalGroup.toPowerSeries : MvFormalGroup g R → _) := by
  rintro ⟨a, _, _, _, _⟩ ⟨b, _, _, _, _⟩ h
  congr

@[scoped simp] theorem toPowerSeries_map (f : R →+* S) (F : MvFormalGroup g R) (i : Fin g) :
    (F.map f).toPowerSeries i = MvPowerSeries.map f (F.toPowerSeries i) := rfl

private theorem _root_.MvFormalGroup.map_map (f : R →+* S) (h : S →+* T) (F : MvFormalGroup g R) :
    (F.map f).map h = F.map (h.comp f) :=
  toPowerSeries_injective (funext fun i => by
    simp only [toPowerSeries_map, MvPowerSeries.map_map])

p2m_export "MvFormalGroup" "map_map"

theorem nthSeries_map (f : R →+* S) (F : MvFormalGroup g R) (n : ℕ) (i : Fin g) :
    (F.map f).nthSeries n i = MvPowerSeries.map f (F.nthSeries n i) := by
  induction n generalizing i with
  | zero => simp [nthSeries_zero]
  | succ n ih =>
    rw [nthSeries_succ, nthSeries_succ]
    have hsub : HasSubst (Sum.elim (F.nthSeries n) fun j => (X j : MvPowerSeries (Fin g) R)) :=
      hasSubst_of_constantCoeff_zero (by
        rintro (j | j)
        · exact constantCoeff_nthSeries F n j
        · exact constantCoeff_X j)
    change subst (Sum.elim ((F.map f).nthSeries n) fun j => X j) (MvPowerSeries.map f (F.toPowerSeries i)) =
      MvPowerSeries.map f (subst (Sum.elim (F.nthSeries n) fun j => X j) (F.toPowerSeries i))
    rw [map_subst hsub]
    congr 1
    funext s
    rcases s with j | j
    · exact ih j
    · simp [map_X]

end MvFormalGroup
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.MvFormalGroup"

p2m_open "MvPowerSeries P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.MvPowerSeries"

namespace MvFormalGroup
p2m_export "MvFormalGroup" "IsComm map nthSeries nthSeries_zero nthSeries_succ mk toPowerSeries constantCoeff_eq_zero constantCoeff_nthSeries adicEval adicEval_mem_radical map_adicEval Points Points.val_zero Points.val_add Points.add_zero algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical"
p2m_open "MvFormalGroup"

p2m_open "MvPowerSeries P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.MvPowerSeries MvPowerSeries.WithPiTopology Filter"

section AdicEvalFinite

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] {σ : Type*}

theorem mvPolynomial_eval₂_eq_sum_of_forall_prod_eq_zero (x : σ → S) (T : Finset (σ →₀ ℕ))
    (hT : ∀ m, m ∉ T → m.prod (fun s e => x s ^ e) = 0) (r : MvPolynomial σ R) :
    MvPolynomial.eval₂ (algebraMap R S) x r =
      ∑ m ∈ T, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) := by
  classical
  rw [MvPolynomial.eval₂_eq]
  change ∑ m ∈ r.support, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) = _
  have h1 : ∑ m ∈ r.support, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) =
      ∑ m ∈ r.support ∪ T, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) :=
    Finset.sum_subset Finset.subset_union_left fun m _ hm => by
      rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, zero_mul]
  have h2 : ∑ m ∈ T, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) =
      ∑ m ∈ r.support ∪ T, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) :=
    Finset.sum_subset Finset.subset_union_right fun m _ hm => by
      rw [hT m hm, mul_zero]
  rw [h1, h2]

theorem adicEval_eq_aeval_of_forall_prod_eq_zero
    (J : Ideal S) (hJ : IsHausdorff J S) (x : σ → S) (F : MvPowerSeries σ R)
    (q : MvPolynomial σ R) (T : Finset (σ →₀ ℕ))
    (hT : ∀ m, m ∉ T → m.prod (fun s e => x s ^ e) = 0)
    (hq : ∀ m ∈ T, MvPolynomial.coeff m q = MvPowerSeries.coeff m F) :
    adicEval J x F = MvPolynomial.aeval x q := by
  classical
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  haveI : T2Space S := (IsAdic.isHausdorff_iff (show IsAdic J from rfl)).mp hJ

  set c : S := ∑ m ∈ T, algebraMap R S (MvPowerSeries.coeff m F) * m.prod (fun s e => x s ^ e)
    with hc
  have key : ∀ r : MvPolynomial σ R,
      (∀ m ∈ T, MvPolynomial.coeff m r = MvPowerSeries.coeff m F) →
      MvPolynomial.eval₂ (algebraMap R S) x r = c := fun r hr => by
    rw [mvPolynomial_eval₂_eq_sum_of_forall_prod_eq_zero x T hT r, hc]
    exact Finset.sum_congr rfl fun m hm => by rw [hr m hm]
  rw [MvPolynomial.aeval_def, key q hq]
  change MvPowerSeries.eval₂ (algebraMap R S) x F = c
  unfold MvPowerSeries.eval₂
  split_ifs with H
  · refine key _ fun m _ => ?_
    rw [← MvPolynomial.coeff_coe, H.choose_spec]
  · refine MvPolynomial.toMvPowerSeries_isDenseInducing.extend_eq_of_tendsto ?_
    have hU : {G : MvPowerSeries σ R | ∀ m ∈ T, MvPowerSeries.coeff m G = MvPowerSeries.coeff m F} ∈
        nhds F := by
      have : {G : MvPowerSeries σ R | ∀ m ∈ T, MvPowerSeries.coeff m G = MvPowerSeries.coeff m F} =
          ⋂ m ∈ T, {G : MvPowerSeries σ R | MvPowerSeries.coeff m G = MvPowerSeries.coeff m F} := by
        ext G
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [this, Filter.biInter_finset_mem]
      intro m _
      exact ((isOpen_discrete ({MvPowerSeries.coeff m F} : Set R)).preimage
        (continuous_coeff (R := R) m)).mem_nhds rfl
    refine Filter.Tendsto.congr' (Filter.mem_of_superset (Filter.preimage_mem_comap hU)
      fun r hr => ?_) tendsto_const_nhds
    exact (key r fun m hm => by rw [← MvPolynomial.coeff_coe]; exact hr m hm).symm

theorem adicEval_eq_adicEval_bot_of_forall_prod_eq_zero
    (J : Ideal S) (hJ : IsHausdorff J S) (x : σ → S) (F : MvPowerSeries σ R)
    (T : Finset (σ →₀ ℕ)) (hT : ∀ m, m ∉ T → m.prod (fun s e => x s ^ e) = 0) :
    adicEval J x F = adicEval ⊥ x F := by
  classical
  have hq : ∀ m ∈ T, MvPolynomial.coeff m (∑ n ∈ T, MvPolynomial.monomial n (MvPowerSeries.coeff n F)) =
      MvPowerSeries.coeff m F := fun m hm => by
    rw [MvPolynomial.coeff_sum, Finset.sum_eq_single m (fun n _ hnm => by
      rw [MvPolynomial.coeff_monomial, if_neg hnm]) (fun h => absurd hm h),
      MvPolynomial.coeff_monomial, if_pos rfl]
  rw [adicEval_eq_aeval_of_forall_prod_eq_zero J hJ x F _ T hT hq,
    adicEval_eq_aeval_of_forall_prod_eq_zero ⊥ inferInstance x F _ T hT hq]

theorem adicEval_eq_aeval_of_degree [Finite σ]
    (J : Ideal S) (hJ : IsHausdorff J S) (x : σ → S) (F : MvPowerSeries σ R)
    (q : MvPolynomial σ R) (N : ℕ)
    (hx : ∀ m : σ →₀ ℕ, N ≤ m.degree → m.prod (fun s e => x s ^ e) = 0)
    (hq : ∀ m : σ →₀ ℕ, m.degree < N → MvPolynomial.coeff m q = MvPowerSeries.coeff m F) :
    adicEval J x F = MvPolynomial.aeval x q := by
  classical
  haveI := Fintype.ofFinite σ
  let d : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N
  have hd : ∀ s, d s = N := fun _ => rfl
  let T : Finset (σ →₀ ℕ) := (Finset.Iic d).filter fun m => m.degree < N
  have hT : ∀ m, m ∉ T → m.prod (fun s e => x s ^ e) = 0 := by
    intro m hm
    refine hx m (not_lt.1 fun hlt => hm ?_)
    refine Finset.mem_filter.2 ⟨Finset.mem_Iic.2 ?_, hlt⟩
    intro s
    rw [hd]
    exact ((Finsupp.le_degree s m).trans hlt.le)
  exact adicEval_eq_aeval_of_forall_prod_eq_zero J hJ x F q T hT
    fun m hm => hq m (Finset.mem_filter.1 hm).2

theorem exists_forall_degree_le_prod_eq_zero_of_isNilpotent [Finite σ]
    (x : σ → S) (hx : ∀ s, IsNilpotent (x s)) :
    ∃ N : ℕ, ∀ m : σ →₀ ℕ, N ≤ m.degree → m.prod (fun s e => x s ^ e) = 0 := by
  classical
  haveI := Fintype.ofFinite σ
  choose k hk using hx
  refine ⟨∑ s, (k s + 1) + 1, fun m hm => ?_⟩

  have hlt : ∑ s, (k s + 1) < ∑ s, m s := by
    rw [← Finsupp.degree_eq_sum]; exact Nat.lt_of_succ_le hm
  obtain ⟨s, -, hs⟩ := Finset.exists_lt_of_sum_lt hlt
  have hms : s ∈ m.support := Finsupp.mem_support_iff.2 (by omega)
  refine Finset.prod_eq_zero hms ?_
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hs.le
  change x s ^ m s = 0
  rw [hr, pow_add, pow_succ, hk s, zero_mul, zero_mul]

end AdicEvalFinite
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.MvFormalGroup"

theorem isHausdorff_span_natCast_of_free
    {𝓞 : Type*} [CommRing 𝓞] (p : ℕ) [hO : IsHausdorff (Ideal.span {(p : 𝓞)}) 𝓞]
    (g : Type*) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] :
    IsHausdorff (Ideal.span {(p : g)}) g := by
  classical
  let b := Module.Free.chooseBasis 𝓞 g
  refine ⟨fun y hy => ?_⟩
  refine b.ext_elem_iff.2 fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine IsHausdorff.haus hO _ fun n => ?_
  have hyn := hy n
  rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
    Ideal.mem_span_singleton'] at hyn ⊢
  obtain ⟨z, hz⟩ := hyn
  refine ⟨b.repr z i, ?_⟩
  have : y = ((p : 𝓞) ^ n) • z := by
    rw [← hz, Algebra.smul_def, map_pow, map_natCast, mul_comm]
  rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]

end MvFormalGroup
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.MvFormalGroup"

namespace MvFormalGroup
p2m_export "MvFormalGroup" "IsComm map nthSeries nthSeries_zero nthSeries_succ mk toPowerSeries constantCoeff_eq_zero constantCoeff_nthSeries adicEval adicEval_mem_radical map_adicEval Points Points.val_zero Points.val_add Points.add_zero algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical"
p2m_open "MvFormalGroup"

p2m_open "MvPowerSeries P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.MvPowerSeries"

section Packaged

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] {σ : Type*}

theorem exists_finset_of_forall_degree_le_prod_eq_zero [Finite σ] (x : σ → S) (N : ℕ)
    (hx : ∀ m : σ →₀ ℕ, N ≤ m.degree → m.prod (fun s e => x s ^ e) = 0) :
    ∃ T : Finset (σ →₀ ℕ), (∀ m, m ∉ T → m.prod (fun s e => x s ^ e) = 0) ∧
      ∀ m ∈ T, m.degree < N := by
  classical
  haveI := Fintype.ofFinite σ
  let d : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N
  have hd : ∀ s, d s = N := fun _ => rfl
  refine ⟨(Finset.Iic d).filter fun m => m.degree < N, fun m hm => ?_,
    fun m hm => (Finset.mem_filter.1 hm).2⟩
  refine hx m (not_lt.1 fun hlt => hm ?_)
  refine Finset.mem_filter.2 ⟨Finset.mem_Iic.2 fun s => ?_, hlt⟩
  rw [hd]
  exact (Finsupp.le_degree s m).trans hlt.le

theorem adicEval_span_natCast_eq_adicEval_bot_of_isNilpotent
    {𝓞 : Type*} [CommRing 𝓞] (p : ℕ) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {g : Type*} [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g]
    {σ : Type*} [Finite σ] {w : σ → g} (hw : ∀ s, IsNilpotent (w s)) (F : MvPowerSeries σ 𝓞) :
    adicEval (Ideal.span {(p : g)}) w F = adicEval ⊥ w F := by
  obtain ⟨N, hN⟩ := exists_forall_degree_le_prod_eq_zero_of_isNilpotent w hw
  obtain ⟨T, hT, -⟩ := exists_finset_of_forall_degree_le_prod_eq_zero w N hN
  exact adicEval_eq_adicEval_bot_of_forall_prod_eq_zero _
    (isHausdorff_span_natCast_of_free (𝓞 := 𝓞) p g) w F T hT

end Packaged
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.MvFormalGroup"

end MvFormalGroup
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.MvFormalGroup"

namespace MvFormalGroup
p2m_export "MvFormalGroup" "IsComm map nthSeries nthSeries_zero nthSeries_succ mk toPowerSeries constantCoeff_eq_zero constantCoeff_nthSeries adicEval adicEval_mem_radical map_adicEval Points Points.val_zero Points.val_add Points.add_zero algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical"
p2m_open "MvFormalGroup"

theorem adicEval_bot_map_algebraMap
    {R R' S σ : Type*} [CommRing R] [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R S]
    [Algebra R' S] [IsScalarTower R R' S] [Finite σ] {w : σ → S} (hw : ∀ s, IsNilpotent (w s))
    (F : MvPowerSeries σ R) :
    adicEval ⊥ w (MvPowerSeries.map (algebraMap R R') F) = adicEval ⊥ w F := by
  classical
  obtain ⟨N, hN⟩ := exists_forall_degree_le_prod_eq_zero_of_isNilpotent w hw
  obtain ⟨T, hT, -⟩ := exists_finset_of_forall_degree_le_prod_eq_zero w N hN
  let q : MvPolynomial σ R := ∑ n ∈ T, MvPolynomial.monomial n (coeff n F)
  have hq : ∀ m ∈ T, MvPolynomial.coeff m q = coeff m F := fun m hm => by
    simp only [q]
    rw [MvPolynomial.coeff_sum, Finset.sum_eq_single m (fun n _ hnm => by
      rw [MvPolynomial.coeff_monomial, if_neg hnm]) (fun h => absurd hm h),
      MvPolynomial.coeff_monomial, if_pos rfl]
  have hq' : ∀ m ∈ T, MvPolynomial.coeff m (MvPolynomial.map (algebraMap R R') q) =
      coeff m (MvPowerSeries.map (algebraMap R R') F) := fun m hm => by
    rw [MvPolynomial.coeff_map, MvPowerSeries.coeff_map, hq m hm]
  rw [adicEval_eq_aeval_of_forall_prod_eq_zero ⊥ inferInstance w _ _ T hT hq',
    adicEval_eq_aeval_of_forall_prod_eq_zero ⊥ inferInstance w F q T hT hq,
    MvPolynomial.aeval_map_algebraMap]

end MvFormalGroup
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.MvFormalGroup"

namespace MvPowerSeries
p2m_export "MvPowerSeries" "map_X coeff coeff_monomial subst C X hasSubst_of_constantCoeff_zero map order monomial map_map coeff_zero map_subst coeff_C_mul constantCoeff_X ext HasSubst coeff_map eval₂ aeval"
p2m_open "MvPowerSeries"

theorem map_surjective_of_surjective {σ R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) : Function.Surjective (MvPowerSeries.map (σ := σ) f) := by
  intro G
  choose g hg using hf
  refine ⟨fun m => g (coeff m G), ?_⟩
  ext m
  rw [coeff_map]
  exact hg _

theorem exists_eq_C_mul_of_forall_coeff_mem_span_singleton {σ R : Type*} [CommRing R] (a : R)
    (F : MvPowerSeries σ R) (h : ∀ m, MvPowerSeries.coeff m F ∈ Ideal.span {a}) :
    ∃ F' : MvPowerSeries σ R, F = MvPowerSeries.C a * F' := by
  choose c hc using fun m => Ideal.mem_span_singleton'.1 (h m)
  refine ⟨fun m => c m, ?_⟩
  ext m
  rw [coeff_C_mul, ← hc m, mul_comm]
  rfl

end MvPowerSeries
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.MvFormalGroup"

namespace MvFormalGroup
p2m_export "MvFormalGroup" "IsComm map nthSeries nthSeries_zero nthSeries_succ mk toPowerSeries constantCoeff_eq_zero constantCoeff_nthSeries adicEval adicEval_mem_radical map_adicEval Points Points.val_zero Points.val_add Points.add_zero algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical"
p2m_open "MvFormalGroup"

section BaseChangeCoalgebra

open scoped TensorProduct

variable (𝓞 S L : Type*) [CommRing 𝓞] [CommRing S] [Algebra 𝓞 S] [CommRing L] [Bialgebra 𝓞 L]

noncomputable def baseChangeTensorHom : L ⊗[𝓞] L →ₐ[𝓞] (S ⊗[𝓞] L) ⊗[S] (S ⊗[𝓞] L) :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft :
        S ⊗[𝓞] L →ₐ[𝓞] (S ⊗[𝓞] L) ⊗[S] (S ⊗[𝓞] L)).comp
      (Algebra.TensorProduct.includeRight : L →ₐ[𝓞] S ⊗[𝓞] L))
    (((Algebra.TensorProduct.includeRight :
        S ⊗[𝓞] L →ₐ[S] (S ⊗[𝓞] L) ⊗[S] (S ⊗[𝓞] L)).restrictScalars 𝓞).comp
      (Algebra.TensorProduct.includeRight : L →ₐ[𝓞] S ⊗[𝓞] L))
    (fun _ _ => @Commute.all ((S ⊗[𝓞] L) ⊗[S] (S ⊗[𝓞] L)) _ _ _)

@[scoped simp] theorem baseChangeTensorHom_tmul (l₁ l₂ : L) :
    baseChangeTensorHom 𝓞 S L (l₁ ⊗ₜ[𝓞] l₂) = ((1 : S) ⊗ₜ[𝓞] l₁) ⊗ₜ[S] ((1 : S) ⊗ₜ[𝓞] l₂) := by
  rw [baseChangeTensorHom, Algebra.TensorProduct.lift_tmul]
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

variable {𝓞 S L}

theorem comul_one_tmul (l : L) :
    Coalgebra.comul (R := S) ((1 : S) ⊗ₜ[𝓞] l) =
      baseChangeTensorHom 𝓞 S L (Coalgebra.comul (R := 𝓞) l) := by
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply]
  induction Coalgebra.comul (R := 𝓞) l using TensorProduct.induction_on with
  | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero]
  | tmul l₁ l₂ =>
    rw [baseChangeTensorHom_tmul, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
  | add x y hx hy => rw [TensorProduct.tmul_add, LinearEquiv.map_add, map_add, hx, hy]

theorem counit_one_tmul (l : L) :
    Coalgebra.counit (R := S) ((1 : S) ⊗ₜ[𝓞] l) = algebraMap 𝓞 S (Coalgebra.counit (R := 𝓞) l) := by
  rw [TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.algebraMap_eq_smul_one]

end BaseChangeCoalgebra
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.MvFormalGroup"

end MvFormalGroup
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.MvFormalGroup"

namespace MvFormalGroup
p2m_export "MvFormalGroup" "IsComm map nthSeries nthSeries_zero nthSeries_succ mk toPowerSeries constantCoeff_eq_zero constantCoeff_nthSeries adicEval adicEval_mem_radical map_adicEval Points Points.val_zero Points.val_add Points.add_zero algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical"
p2m_open "MvFormalGroup"

theorem adicEval_sumElim_zero {g : ℕ} {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (F : MvFormalGroup g R) (J : Ideal S) [IsAdicComplete J S] {x : Fin g → S}
    (hx : ∀ j, x j ∈ J.radical) (i : Fin g) :
    adicEval J (Sum.elim x (fun _ => (0 : S))) (F.toPowerSeries i) = x i := by
  have h := congrArg (fun P : Points F S J => P.val i) (Points.add_zero (⟨x, hx⟩ : Points F S J))
  simpa only [Points.val_add, Points.val_zero] using h

end MvFormalGroup
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.MvFormalGroup"

noncomputable section

namespace Deformation
p2m_export "Deformation" "HondaSystem DieudonneModule HondaSystem.SplitCoordinates"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk L SplitCoordinates"
namespace LVd
p2m_open "Deformation.HondaSystem Deformation"

section Generic

variable (p : ℕ)

theorem natCast_eq_zero (A : Type*) [Ring A] [Algebra (ZMod p) A] : (p : A) = 0 := by
  rw [← map_natCast (algebraMap (ZMod p) A), ZMod.natCast_self, map_zero]

theorem span_natCast_eq_bot (A : Type*) [Ring A] [Algebra (ZMod p) A] :
    Ideal.span {(p : A)} = ⊥ :=
  Ideal.span_singleton_eq_bot.2 (natCast_eq_zero p A)

variable {p}

theorem isNilpotent_of_mem_radical_span_natCast {A : Type*} [CommRing A] [Algebra (ZMod p) A] {x : A}
    (hx : x ∈ (Ideal.span {(p : A)}).radical) : IsNilpotent x := by
  rw [span_natCast_eq_bot p A] at hx
  obtain ⟨n, hn⟩ := hx
  exact ⟨n, (Ideal.mem_bot).1 hn⟩

theorem mem_radical_bot_of_isNilpotent {A : Type*} [CommSemiring A] {x : A} (hx : IsNilpotent x) :
    x ∈ (⊥ : Ideal A).radical := by
  obtain ⟨n, hn⟩ := hx
  exact ⟨n, by rw [hn]; exact Ideal.zero_mem _⟩

theorem map_mem_radical_span_natCast (p : ℕ) {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {x : A}
    (hx : x ∈ (Ideal.span {(p : A)}).radical) : φ x ∈ (Ideal.span {(p : B)}).radical := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
  refine ⟨n, Ideal.mem_span_singleton'.2 ⟨φ c, ?_⟩⟩
  rw [← map_pow, ← hc, map_mul, map_natCast]

theorem algHom_ext_of_isNilpotent {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {σ : Type*} [Finite σ]
    {ψ₁ ψ₂ : MvPowerSeries σ R →ₐ[R] S} (h : ∀ s, ψ₁ (X s) = ψ₂ (X s))
    (hn : ∀ s, IsNilpotent (ψ₁ (X s))) : ψ₁ = ψ₂ := by
  apply AlgHom.ext
  intro f
  have h1 : ∀ s, ψ₁ (X s) ∈ (⊥ : Ideal S).radical := fun s => mem_radical_bot_of_isNilpotent (hn s)
  have h2 : ∀ s, ψ₂ (X s) ∈ (⊥ : Ideal S).radical := fun s => by
    rw [← h s]
    exact h1 s
  rw [MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical ⊥ ψ₁ h1 f,
    MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical ⊥ ψ₂ h2 f]
  exact congrArg (fun w => MvFormalGroup.adicEval ⊥ w f) (funext h)

theorem algHom_eq_of_comp_eq {R A B C : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
    [Algebra R A] [Algebra R B] [Algebra R C] {κ : A →ₐ[R] B} (hκ : Function.Surjective κ)
    {g₁ g₂ : B →ₐ[R] C} (h : g₁.comp κ = g₂.comp κ) : g₁ = g₂ :=
  AlgHom.ext fun b => by
    obtain ⟨a, rfl⟩ := hκ b
    exact DFunLike.congr_fun h a

def algHomOfRingHom (p : ℕ) {A B : Type*} [Ring A] [Ring B] [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (f : A →+* B) : A →ₐ[ZMod p] B :=
  { f with
    commutes' := fun c =>
      DFunLike.congr_fun (Subsingleton.elim (f.comp (algebraMap (ZMod p) A)) (algebraMap (ZMod p) B)) c }

@[scoped simp]
theorem algHomOfRingHom_apply (p : ℕ) {A B : Type*} [Ring A] [Ring B] [Algebra (ZMod p) A]
    [Algebra (ZMod p) B] (f : A →+* B) (a : A) : algHomOfRingHom p f a = f a :=
  rfl

end Generic
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.MvFormalGroup"

section Level

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
  (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
  {d : ℕ} {L : Type u} [CommRing L] [Bialgebra 𝓞 L] (Ψ : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] L)

abbrev red (n : ℕ) : MvPowerSeries (Fin n) 𝓞 →+* MvPowerSeries (Fin n) (ZMod p) :=
  MvPowerSeries.map (algebraMap 𝓞 (ZMod p))

theorem red_surjective (n : ℕ) : Function.Surjective (red p n (𝓞 := 𝓞)) :=
  MvPowerSeries.map_surjective_of_surjective _ (ZMod.ringHom_surjective _)

theorem one_tmul_eq_zero_of_mem_span {y : L} (hy : y ∈ Ideal.span {(p : L)}) :
    (1 : ZMod p) ⊗ₜ[𝓞] y = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  show (Algebra.TensorProduct.includeRight : L →ₐ[𝓞] ZMod p ⊗[𝓞] L) (c * ↑p) = 0
  rw [map_mul, map_natCast, natCast_eq_zero p (ZMod p ⊗[𝓞] L), mul_zero]

include hker in

theorem mem_span_of_one_tmul_eq_zero {y : L} (h : (1 : ZMod p) ⊗ₜ[𝓞] y = 0) :
    y ∈ Ideal.span {(p : L)} := by
  have hsurj : Function.Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _
  have hle : RingHom.ker (algebraMap 𝓞 (ZMod p)) ≤
      RingHom.ker ((Ideal.Quotient.mk (Ideal.span {(p : L)})).comp (algebraMap 𝓞 L)) := by
    rw [hker, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      RingHom.comp_apply, map_natCast, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  let χ : ZMod p →+* L ⧸ Ideal.span {(p : L)} :=
    (algebraMap 𝓞 (ZMod p)).liftOfSurjective hsurj ⟨_, hle⟩
  have hχ : ∀ a, χ (algebraMap 𝓞 (ZMod p) a) = Ideal.Quotient.mk _ (algebraMap 𝓞 L a) :=
    fun a => (algebraMap 𝓞 (ZMod p)).liftOfRightInverse_comp_apply _ _ _ a
  let χₐ : ZMod p →ₐ[𝓞] L ⧸ Ideal.span {(p : L)} :=
    { χ with
      commutes' := fun a => by
        change χ (algebraMap 𝓞 (ZMod p) a) = _
        rw [hχ, Ideal.Quotient.mk_algebraMap] }
  let Λ : ZMod p ⊗[𝓞] L →ₐ[𝓞] L ⧸ Ideal.span {(p : L)} :=
    Algebra.TensorProduct.lift χₐ (Ideal.Quotient.mkₐ 𝓞 (Ideal.span {(p : L)})) (fun _ _ => Commute.all _ _)
  have hΛ : Λ ((1 : ZMod p) ⊗ₜ[𝓞] y) = Ideal.Quotient.mk _ y := by
    change Algebra.TensorProduct.lift χₐ _ _ ((1 : ZMod p) ⊗ₜ[𝓞] y) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← hΛ, h, map_zero]

include hker in
theorem ker_red_le :
    RingHom.ker (red p d (𝓞 := 𝓞)) ≤
      RingHom.ker ((Algebra.TensorProduct.includeRight :
        L →ₐ[𝓞] ZMod p ⊗[𝓞] L).toRingHom.comp Ψ.toRingHom) := by
  intro F hF
  rw [RingHom.mem_ker] at hF ⊢
  have hcoeff : ∀ m, MvPowerSeries.coeff m F ∈ Ideal.span {(p : 𝓞)} := fun m => by
    rw [← hker, RingHom.mem_ker, ← MvPowerSeries.coeff_map, hF, MvPowerSeries.coeff_zero]
  obtain ⟨F', rfl⟩ := MvPowerSeries.exists_eq_C_mul_of_forall_coeff_mem_span_singleton _ F hcoeff
  rw [RingHom.comp_apply, map_natCast, map_mul, map_natCast, map_mul, map_natCast,
    natCast_eq_zero p (ZMod p ⊗[𝓞] L), zero_mul]

include hker Ψ in

def ψ : MvPowerSeries (Fin d) (ZMod p) →+* ZMod p ⊗[𝓞] L :=
  (red p d).liftOfRightInverse (Function.surjInv (red_surjective p d))
    (Function.rightInverse_surjInv (red_surjective p d))
    ⟨(Algebra.TensorProduct.includeRight : L →ₐ[𝓞] ZMod p ⊗[𝓞] L).toRingHom.comp Ψ.toRingHom,
      ker_red_le p hker Ψ⟩

theorem ψ_red (F : MvPowerSeries (Fin d) 𝓞) :
    ψ p hker Ψ (red p d F) = (1 : ZMod p) ⊗ₜ[𝓞] Ψ F := by
  rw [ψ, RingHom.liftOfRightInverse_comp_apply]
  rfl

variable (Φ : MvFormalGroup d 𝓞) (v : ℕ)
  (hΨtors : ∀ i, Ψ (Φ.nthSeries (p ^ v) i) ∈ Ideal.span {(p : L)})
  {G : Type v} [CommRing G] [Bialgebra (ZMod p) G]
  (κ : MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] G) (hκs : Function.Surjective κ)
  (Φ₀ : MvFormalGroup d (ZMod p)) (hΦ₀ : Φ.map (algebraMap 𝓞 (ZMod p)) = Φ₀)
  (hkerκ : RingHom.ker κ = Ideal.span (Set.range (Φ₀.nthSeries (p ^ v))))

include hΨtors hΦ₀ hkerκ in

theorem ker_κ_le : RingHom.ker (κ : MvPowerSeries (Fin d) (ZMod p) →+* G) ≤ RingHom.ker (ψ p hker Ψ) := by
  intro F hF
  have hF' : F ∈ RingHom.ker κ := hF
  rw [hkerκ, ← hΦ₀] at hF'
  refine Submodule.span_induction (p := fun F _ => F ∈ RingHom.ker (ψ p hker Ψ)) ?_ ?_ ?_ ?_ hF'
  · rintro _ ⟨i, rfl⟩
    rw [RingHom.mem_ker, MvFormalGroup.nthSeries_map]
    change ψ p hker Ψ (red p d (Φ.nthSeries (p ^ v) i)) = 0
    rw [ψ_red]
    exact one_tmul_eq_zero_of_mem_span p (hΨtors i)
  · exact Ideal.zero_mem _
  · intro x y _ _ hx hy
    exact Ideal.add_mem _ hx hy
  · intro a x _ hx
    exact Ideal.mul_mem_left _ a hx

include hker Ψ Φ v hΨtors hκs Φ₀ hΦ₀ hkerκ in

def e : G →ₐ[ZMod p] ZMod p ⊗[𝓞] L :=
  algHomOfRingHom p
    ((κ : MvPowerSeries (Fin d) (ZMod p) →+* G).liftOfRightInverse (Function.surjInv hκs)
      (Function.rightInverse_surjInv hκs)
      ⟨ψ p hker Ψ, ker_κ_le p hker Ψ Φ v hΨtors κ Φ₀ hΦ₀ hkerκ⟩)

theorem e_κ (F : MvPowerSeries (Fin d) (ZMod p)) :
    e p hker Ψ Φ v hΨtors κ hκs Φ₀ hΦ₀ hkerκ (κ F) = ψ p hker Ψ F := by
  rw [e, algHomOfRingHom_apply]
  exact (κ : MvPowerSeries (Fin d) (ZMod p) →+* G).liftOfRightInverse_comp_apply _ _ _ F

theorem e_κ_red (F : MvPowerSeries (Fin d) 𝓞) :
    e p hker Ψ Φ v hΨtors κ hκs Φ₀ hΦ₀ hkerκ (κ (red p d F)) = (1 : ZMod p) ⊗ₜ[𝓞] Ψ F := by
  rw [e_κ, ψ_red]

theorem e_κ_X (i : Fin d) :
    e p hker Ψ Φ v hΨtors κ hκs Φ₀ hΦ₀ hkerκ (κ (X i)) = (1 : ZMod p) ⊗ₜ[𝓞] Ψ (X i) := by
  have h := e_κ_red p hker Ψ Φ v hΨtors κ hκs Φ₀ hΦ₀ hkerκ (X i)
  rwa [show red p d (X i) = X i from MvPowerSeries.map_X _ i] at h

theorem isNilpotent_κ_X (hκrad : ∀ i, κ (X i) ∈ (Ideal.span {(p : G)}).radical) (i : Fin d) :
    IsNilpotent (κ (X i)) :=
  isNilpotent_of_mem_radical_span_natCast (hκrad i)

include hker hΨtors hκs hΦ₀ hkerκ in

theorem apply_X_mem_radical (hκrad : ∀ i, κ (X i) ∈ (Ideal.span {(p : G)}).radical) (i : Fin d) :
    Ψ (X i) ∈ (Ideal.span {(p : L)}).radical := by
  obtain ⟨n, hn⟩ := (isNilpotent_κ_X p κ hκrad i).map (e p hker Ψ Φ v hΨtors κ hκs Φ₀ hΦ₀ hkerκ)
  rw [e_κ_X, Algebra.TensorProduct.tmul_pow, one_pow] at hn
  exact ⟨n, mem_span_of_one_tmul_eq_zero p hker hn⟩

theorem baseChange_adicEval_twist [IsAdicComplete (Ideal.span {(p : L ⊗[𝓞] L)}) (L ⊗[𝓞] L)]
    (hrad : ∀ i, Ψ (X i) ∈ (Ideal.span {(p : L)}).radical)
    (C : Fin d → L ⊗[𝓞] L) (hC : ∀ j, C j ∈ Ideal.span {(p : L ⊗[𝓞] L)}) (i : Fin d) :
    MvFormalGroup.baseChangeTensorHom 𝓞 (ZMod p) L
      (MvFormalGroup.adicEval (Ideal.span {(p : L ⊗[𝓞] L)})
        (Sum.elim (fun j => Ψ (X j) ⊗ₜ[𝓞] (1 : L))
          (fun j => MvFormalGroup.adicEval (Ideal.span {(p : L ⊗[𝓞] L)})
            (Sum.elim (fun j => (1 : L) ⊗ₜ[𝓞] Ψ (X j)) C) (Φ.toPowerSeries j)))
        (Φ.toPowerSeries i)) =
    MvFormalGroup.adicEval (⊥ : Ideal ((ZMod p ⊗[𝓞] L) ⊗[ZMod p] (ZMod p ⊗[𝓞] L)))
      (Sum.elim (fun j => ((1 : ZMod p) ⊗ₜ[𝓞] Ψ (X j)) ⊗ₜ[ZMod p] (1 : ZMod p ⊗[𝓞] L))
        (fun j => (1 : ZMod p ⊗[𝓞] L) ⊗ₜ[ZMod p] ((1 : ZMod p) ⊗ₜ[𝓞] Ψ (X j))))
      (Φ.toPowerSeries i) := by

  have hβ0 : ∀ s ∈ Ideal.span {(p : L ⊗[𝓞] L)},
      MvFormalGroup.baseChangeTensorHom 𝓞 (ZMod p) L s = 0 := fun s hs => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hs
    rw [map_mul, map_natCast, natCast_eq_zero p ((ZMod p ⊗[𝓞] L) ⊗[ZMod p] (ZMod p ⊗[𝓞] L)),
      mul_zero]
  have step2 : ∀ (x : Fin d ⊕ Fin d → L ⊗[𝓞] L) (_ : ∀ s, x s ∈ (Ideal.span {(p : L ⊗[𝓞] L)}).radical)
      (f : MvPowerSeries (Fin d ⊕ Fin d) 𝓞),
      MvFormalGroup.baseChangeTensorHom 𝓞 (ZMod p) L
        (MvFormalGroup.adicEval (Ideal.span {(p : L ⊗[𝓞] L)}) x f) =
      MvFormalGroup.adicEval (⊥ : Ideal ((ZMod p ⊗[𝓞] L) ⊗[ZMod p] (ZMod p ⊗[𝓞] L)))
        (fun s => MvFormalGroup.baseChangeTensorHom 𝓞 (ZMod p) L (x s)) f :=
    fun x hx f => MvFormalGroup.map_adicEval (R := 𝓞) (S := L ⊗[𝓞] L)
      (S' := (ZMod p ⊗[𝓞] L) ⊗[ZMod p] (ZMod p ⊗[𝓞] L)) (Ideal.span {(p : L ⊗[𝓞] L)}) ⊥
      (MvFormalGroup.baseChangeTensorHom 𝓞 (ZMod p) L) (Submodule.fg_span_singleton _) (fun s hs => by rw [hβ0 s hs]; exact Ideal.zero_mem _) hx f

  have hinner : ∀ s, Sum.elim (fun j => (1 : L) ⊗ₜ[𝓞] Ψ (X j)) C s ∈
      (Ideal.span {(p : L ⊗[𝓞] L)}).radical := by
    rintro (j | j)
    · exact map_mem_radical_span_natCast p
        (Algebra.TensorProduct.includeRight : L →ₐ[𝓞] L ⊗[𝓞] L).toRingHom (hrad j)
    · exact Ideal.le_radical (hC j)
  have houter : ∀ s, Sum.elim (fun j => Ψ (X j) ⊗ₜ[𝓞] (1 : L))
      (fun j => MvFormalGroup.adicEval (Ideal.span {(p : L ⊗[𝓞] L)})
        (Sum.elim (fun j => (1 : L) ⊗ₜ[𝓞] Ψ (X j)) C) (Φ.toPowerSeries j)) s ∈
      (Ideal.span {(p : L ⊗[𝓞] L)}).radical := by
    rintro (j | j)
    · exact map_mem_radical_span_natCast p
        (Algebra.TensorProduct.includeLeft : L →ₐ[𝓞] L ⊗[𝓞] L).toRingHom (hrad j)
    · exact MvFormalGroup.adicEval_mem_radical _ hinner (Φ.constantCoeff_eq_zero j)
  have hWn : ∀ j, IsNilpotent ((1 : ZMod p ⊗[𝓞] L) ⊗ₜ[ZMod p] ((1 : ZMod p) ⊗ₜ[𝓞] Ψ (X j))) :=
    fun j => by
    obtain ⟨n, hn⟩ := hrad j
    refine ⟨n, ?_⟩
    rw [Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_pow, one_pow,
      one_tmul_eq_zero_of_mem_span p hn, TensorProduct.tmul_zero]
  rw [step2 _ houter]
  congr 1
  funext s
  rcases s with j | j
  · simp only [Sum.elim_inl, MvFormalGroup.baseChangeTensorHom_tmul]
    rfl
  · simp only [Sum.elim_inr]
    rw [step2 _ hinner]
    have hY : (fun s => MvFormalGroup.baseChangeTensorHom 𝓞 (ZMod p) L
        (Sum.elim (fun j => (1 : L) ⊗ₜ[𝓞] Ψ (X j)) C s)) =
        Sum.elim (fun j => (1 : ZMod p ⊗[𝓞] L) ⊗ₜ[ZMod p] ((1 : ZMod p) ⊗ₜ[𝓞] Ψ (X j)))
          (fun _ => 0) := by
      funext s
      rcases s with j' | j'
      · simp only [Sum.elim_inl, MvFormalGroup.baseChangeTensorHom_tmul]
        rfl
      · simp only [Sum.elim_inr]
        exact hβ0 _ (hC j')
    rw [hY, MvFormalGroup.adicEval_sumElim_zero Φ ⊥ (fun j => mem_radical_bot_of_isNilpotent (hWn j)) j]

theorem counit_comp_e (hκrad : ∀ i, κ (X i) ∈ (Ideal.span {(p : G)}).radical)
    (hcounitκ : ∀ i, Coalgebra.counit (R := ZMod p) (κ (X i)) = 0)
    (hΨε : ∀ i, Coalgebra.counit (R := 𝓞) (Ψ (X i)) = 0) :
    (Bialgebra.counitAlgHom (ZMod p) (ZMod p ⊗[𝓞] L)).comp (e p hker Ψ Φ v hΨtors κ hκs Φ₀ hΦ₀ hkerκ) =
      Bialgebra.counitAlgHom (ZMod p) G := by
  apply algHom_eq_of_comp_eq hκs
  refine algHom_ext_of_isNilpotent (R := ZMod p) (S := ZMod p) ?_ ?_
  · intro i
    simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply]
    rw [hcounitκ, e_κ_X, MvFormalGroup.counit_one_tmul, hΨε, map_zero]
  · intro i
    exact (isNilpotent_κ_X p κ hκrad i).map
      ((Bialgebra.counitAlgHom (ZMod p) (ZMod p ⊗[𝓞] L)).comp (e p hker Ψ Φ v hΨtors κ hκs Φ₀ hΦ₀ hkerκ))

variable {Et : Type u} [CommRing Et] [Bialgebra 𝓞 Et] (ι : Et →ₐc[𝓞] L) (c₂ : Fin d → Et ⊗[𝓞] Et)

theorem comul_comp_e [IsAdicComplete (Ideal.span {(p : L ⊗[𝓞] L)}) (L ⊗[𝓞] L)]
    (hκrad : ∀ i, κ (X i) ∈ (Ideal.span {(p : G)}).radical)
    (hcomulκ : ∀ i, Coalgebra.comul (R := ZMod p) (κ (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : G ⊗[ZMod p] G)})
        (Sum.elim (fun j => κ (X j) ⊗ₜ[ZMod p] (1 : G)) (fun j => (1 : G) ⊗ₜ[ZMod p] κ (X j)))
        (Φ₀.toPowerSeries i))
    (hc₂p : ∀ i, c₂ i ∈ Ideal.span {(p : Et ⊗[𝓞] Et)})
    (hcomul : ∀ i, Coalgebra.comul (R := 𝓞) (Ψ (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : L ⊗[𝓞] L)})
        (Sum.elim (fun j => Ψ (X j) ⊗ₜ[𝓞] (1 : L))
          (fun j => MvFormalGroup.adicEval (Ideal.span {(p : L ⊗[𝓞] L)})
            (Sum.elim (fun j => (1 : L) ⊗ₜ[𝓞] Ψ (X j))
              (fun j => Algebra.TensorProduct.map (ι : Et →ₐ[𝓞] L) (ι : Et →ₐ[𝓞] L) (c₂ j)))
            (Φ.toPowerSeries j)))
        (Φ.toPowerSeries i)) :
    (Algebra.TensorProduct.map (e p hker Ψ Φ v hΨtors κ hκs Φ₀ hΦ₀ hkerκ)
        (e p hker Ψ Φ v hΨtors κ hκs Φ₀ hΦ₀ hkerκ)).comp (Bialgebra.comulAlgHom (ZMod p) G) =
      (Bialgebra.comulAlgHom (ZMod p) (ZMod p ⊗[𝓞] L)).comp (e p hker Ψ Φ v hΨtors κ hκs Φ₀ hΦ₀ hkerκ) := by

  set E := e p hker Ψ Φ v hΨtors κ hκs Φ₀ hΦ₀ hkerκ with hE
  have hκn : ∀ i, IsNilpotent (κ (X i)) := isNilpotent_κ_X p κ hκrad
  have hrad : ∀ i, Ψ (X i) ∈ (Ideal.span {(p : L)}).radical :=
    apply_X_mem_radical p hker Ψ Φ v hΨtors κ hκs Φ₀ hΦ₀ hkerκ hκrad

  set W : Fin d ⊕ Fin d → (ZMod p ⊗[𝓞] L) ⊗[ZMod p] (ZMod p ⊗[𝓞] L) :=
    Sum.elim (fun j => ((1 : ZMod p) ⊗ₜ[𝓞] Ψ (X j)) ⊗ₜ[ZMod p] (1 : ZMod p ⊗[𝓞] L))
      (fun j => (1 : ZMod p ⊗[𝓞] L) ⊗ₜ[ZMod p] ((1 : ZMod p) ⊗ₜ[𝓞] Ψ (X j))) with hW
  have hWn : ∀ s, IsNilpotent (W s) := by
    have h1 : ∀ j, IsNilpotent ((1 : ZMod p) ⊗ₜ[𝓞] Ψ (X j)) := fun j => by
      rw [← e_κ_X p hker Ψ Φ v hΨtors κ hκs Φ₀ hΦ₀ hkerκ]
      exact (hκn j).map _
    rintro (j | j)
    · exact (h1 j).map (Algebra.TensorProduct.includeLeft :
        ZMod p ⊗[𝓞] L →ₐ[ZMod p] (ZMod p ⊗[𝓞] L) ⊗[ZMod p] (ZMod p ⊗[𝓞] L))
    · exact (h1 j).map (Algebra.TensorProduct.includeRight :
        ZMod p ⊗[𝓞] L →ₐ[ZMod p] (ZMod p ⊗[𝓞] L) ⊗[ZMod p] (ZMod p ⊗[𝓞] L))
  apply algHom_eq_of_comp_eq hκs
  refine algHom_ext_of_isNilpotent (R := ZMod p)
    (S := (ZMod p ⊗[𝓞] L) ⊗[ZMod p] (ZMod p ⊗[𝓞] L)) (fun i => ?_) (fun i => (hκn i).map
      ((Algebra.TensorProduct.map E E).comp (Bialgebra.comulAlgHom (ZMod p) G)))
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
  rw [hcomulκ, span_natCast_eq_bot p (G ⊗[ZMod p] G)]

  have step1 : ∀ f : MvPowerSeries (Fin d ⊕ Fin d) (ZMod p),
      Algebra.TensorProduct.map E E (MvFormalGroup.adicEval (⊥ : Ideal (G ⊗[ZMod p] G))
        (Sum.elim (fun j => κ (X j) ⊗ₜ[ZMod p] (1 : G)) (fun j => (1 : G) ⊗ₜ[ZMod p] κ (X j))) f) =
      MvFormalGroup.adicEval (⊥ : Ideal ((ZMod p ⊗[𝓞] L) ⊗[ZMod p] (ZMod p ⊗[𝓞] L)))
        (fun s => Algebra.TensorProduct.map E E
          (Sum.elim (fun j => κ (X j) ⊗ₜ[ZMod p] (1 : G)) (fun j => (1 : G) ⊗ₜ[ZMod p] κ (X j)) s)) f :=
    fun f => MvFormalGroup.map_adicEval (R := ZMod p) (S := G ⊗[ZMod p] G)
      (S' := (ZMod p ⊗[𝓞] L) ⊗[ZMod p] (ZMod p ⊗[𝓞] L)) ⊥ ⊥ (Algebra.TensorProduct.map E E)
      Submodule.fg_bot
      (fun s hs => by rw [(Ideal.mem_bot).1 hs, map_zero]; exact Ideal.zero_mem _)
      (by
        rintro (j | j)
        · exact mem_radical_bot_of_isNilpotent ((hκn j).map
            (Algebra.TensorProduct.includeLeft : G →ₐ[ZMod p] G ⊗[ZMod p] G))
        · exact mem_radical_bot_of_isNilpotent ((hκn j).map
            (Algebra.TensorProduct.includeRight : G →ₐ[ZMod p] G ⊗[ZMod p] G))) f
  refine (step1 _).trans ?_
  have hL : (fun s => Algebra.TensorProduct.map E E
      (Sum.elim (fun j => κ (X j) ⊗ₜ[ZMod p] (1 : G)) (fun j => (1 : G) ⊗ₜ[ZMod p] κ (X j)) s)) = W := by
    funext s
    rcases s with j | j
    · simp only [Sum.elim_inl, Algebra.TensorProduct.map_tmul, map_one, hE, e_κ_X, hW]
    · simp only [Sum.elim_inr, Algebra.TensorProduct.map_tmul, map_one, hE, e_κ_X, hW]
  rw [hL, ← hΦ₀]
  change MvFormalGroup.adicEval ⊥ W (MvPowerSeries.map (algebraMap 𝓞 (ZMod p)) (Φ.toPowerSeries i)) = _
  rw [MvFormalGroup.adicEval_bot_map_algebraMap hWn]

  have hC : ∀ j, Algebra.TensorProduct.map (ι : Et →ₐ[𝓞] L) (ι : Et →ₐ[𝓞] L) (c₂ j) ∈
      Ideal.span {(p : L ⊗[𝓞] L)} := fun j => by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hc₂p j)
    rw [← hc, map_mul, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  rw [hE, e_κ_X, MvFormalGroup.comul_one_tmul, hcomul,
    baseChange_adicEval_twist p Ψ Φ hrad _ hC i, hW]

def ee [IsAdicComplete (Ideal.span {(p : L ⊗[𝓞] L)}) (L ⊗[𝓞] L)]
    (hκrad : ∀ i, κ (X i) ∈ (Ideal.span {(p : G)}).radical)
    (hcounitκ : ∀ i, Coalgebra.counit (R := ZMod p) (κ (X i)) = 0)
    (hcomulκ : ∀ i, Coalgebra.comul (R := ZMod p) (κ (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : G ⊗[ZMod p] G)})
        (Sum.elim (fun j => κ (X j) ⊗ₜ[ZMod p] (1 : G)) (fun j => (1 : G) ⊗ₜ[ZMod p] κ (X j)))
        (Φ₀.toPowerSeries i))
    (hΨε : ∀ i, Coalgebra.counit (R := 𝓞) (Ψ (X i)) = 0)
    (hc₂p : ∀ i, c₂ i ∈ Ideal.span {(p : Et ⊗[𝓞] Et)})
    (hcomul : ∀ i, Coalgebra.comul (R := 𝓞) (Ψ (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : L ⊗[𝓞] L)})
        (Sum.elim (fun j => Ψ (X j) ⊗ₜ[𝓞] (1 : L))
          (fun j => MvFormalGroup.adicEval (Ideal.span {(p : L ⊗[𝓞] L)})
            (Sum.elim (fun j => (1 : L) ⊗ₜ[𝓞] Ψ (X j))
              (fun j => Algebra.TensorProduct.map (ι : Et →ₐ[𝓞] L) (ι : Et →ₐ[𝓞] L) (c₂ j)))
            (Φ.toPowerSeries j)))
        (Φ.toPowerSeries i)) :
    G →ₐc[ZMod p] ZMod p ⊗[𝓞] L :=
  BialgHom.ofAlgHom (e p hker Ψ Φ v hΨtors κ hκs Φ₀ hΦ₀ hkerκ)
    (counit_comp_e p hker Ψ Φ v hΨtors κ hκs Φ₀ hΦ₀ hkerκ hκrad hcounitκ hΨε)
    (comul_comp_e p hker Ψ Φ v hΨtors κ hκs Φ₀ hΦ₀ hkerκ ι c₂ hκrad hcomulκ hc₂p hcomul)

end Level
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.MvFormalGroup"

section Etale

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
  {L : Type u} [CommRing L] [Bialgebra 𝓞 L]
  {Gc : Type v} [CommRing Gc] [Bialgebra (ZMod p) Gc]
  {Ge : Type v} [CommRing Ge] [Bialgebra (ZMod p) Ge]
  {Et : Type u} [CommRing Et] [Bialgebra 𝓞 Et]
  (ec : Gc →ₐc[ZMod p] ZMod p ⊗[𝓞] L) (ι : Et →ₐc[𝓞] L)
  (θe : ZMod p ⊗[𝓞] Et →ₐc[ZMod p] Ge) (hθe : Function.Bijective θe)

def eEt : Ge →ₐc[ZMod p] ZMod p ⊗[𝓞] L :=
  (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ι).comp
    ((BialgEquiv.ofBijective θe hθe).symm : Ge →ₐc[ZMod p] ZMod p ⊗[𝓞] Et)

theorem eEt_θe (z : ZMod p ⊗[𝓞] Et) :
    eEt p ι θe hθe (θe z) = Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ι z := by
  change Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ι
    ((BialgEquiv.ofBijective θe hθe).symm (BialgEquiv.ofBijective θe hθe z)) = _
  rw [BialgEquiv.symm_apply_apply]

theorem eEt_θe_tmul (c : ZMod p) (y : Et) :
    eEt p ι θe hθe (θe (c ⊗ₜ[𝓞] y)) = c ⊗ₜ[𝓞] ι y := by
  rw [eEt_θe, Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply]

def eeT : Gc ⊗[ZMod p] Ge →ₐc[ZMod p] ZMod p ⊗[𝓞] L :=
  (Bialgebra.mulBialgHom (ZMod p) (ZMod p ⊗[𝓞] L)).comp
    (Bialgebra.TensorProduct.map ec (eEt p ι θe hθe))

theorem eeT_tmul (a : Gc) (b : Ge) :
    eeT p ec ι θe hθe (a ⊗ₜ[ZMod p] b) = ec a * eEt p ι θe hθe b := by
  change Bialgebra.mulBialgHom (ZMod p) (ZMod p ⊗[𝓞] L)
    (Bialgebra.TensorProduct.map ec (eEt p ι θe hθe) (a ⊗ₜ[ZMod p] b)) = _
  rw [Bialgebra.TensorProduct.map_tmul, Bialgebra.coe_mulBialgHom, LinearMap.mul'_apply]

end Etale
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.MvFormalGroup"

end Deformation.HondaSystem.LVd
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.MvFormalGroup P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.Deformation P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.Deformation.HondaSystem P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.Deformation.HondaSystem.LVd"
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.MvFormalGroup P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.Deformation P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.Deformation.HondaSystem"
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.MvFormalGroup P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.Deformation"

end
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.MvFormalGroup P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.Deformation P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.Deformation.HondaSystem P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.Deformation.HondaSystem.LVd"

open _root_.Deformation.HondaSystem _root_.P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle.Deformation.HondaSystem in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v)
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v))

    (𝒮 : Deformation.HondaSystem.SplitCoordinates p r H₁ G s π) (h𝒮 : 𝒮.Lawful)
    (Φ : MvFormalGroup 𝒮.d 𝓞) [Φ.IsComm] (hΦ : Φ.map (algebraMap 𝓞 (ZMod p)) = 𝒮.Φ₀)
    (c₂ : ∀ v, Fin 𝒮.d → 𝒮.Et v ⊗[𝓞] 𝒮.Et v)
    (hc₂p : ∀ v i, c₂ v i ∈ Ideal.span {(p : 𝒮.Et v ⊗[𝓞] 𝒮.Et v)})

    (L : ℕ → Type u) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra 𝓞 (L v)]
    [∀ v, Module.Free 𝓞 (L v)] [∀ v, Module.Finite 𝓞 (L v)]
    (t : ∀ v, L (v + 1) →ₐc[𝓞] L v) (ι : ∀ v, 𝒮.Et v →ₐc[𝓞] L v)
    (Ψ : ∀ v, MvPowerSeries (Fin 𝒮.d) 𝓞 →ₐ[𝓞] L v)
    (hrankL : ∀ v, Module.finrank 𝓞 (L v) = p ^ (v * (𝒮.hc + 𝒮.he)))
    (hιt : ∀ v, (t v).comp (ι (v + 1)) = (ι v).comp (𝒮.st v))
    (hΨt : ∀ v, ((t v : L (v + 1) →ₐc[𝓞] L v) : L (v + 1) →ₐ[𝓞] L v).comp (Ψ (v + 1)) = Ψ v)
    (hΨε : ∀ v i, Coalgebra.counit (R := 𝓞) (Ψ v (X i)) = 0)
    (hΨtors : ∀ v i, Ψ v (Φ.nthSeries (p ^ v) i) ∈ Ideal.span {(p : L v)})
    (hgen : ∀ v, Function.Surjective
        (Algebra.TensorProduct.lift (ι v : 𝒮.Et v →ₐ[𝓞] L v) (Ψ v) (fun _ _ => Commute.all _ _)))
    (hcomul : ∀ v i, Coalgebra.comul (R := 𝓞) (Ψ v (X i)) =
        MvFormalGroup.adicEval (Ideal.span {(p : L v ⊗[𝓞] L v)})
          (Sum.elim (fun j => Ψ v (X j) ⊗ₜ[𝓞] (1 : L v))
            (fun j => MvFormalGroup.adicEval (Ideal.span {(p : L v ⊗[𝓞] L v)})
              (Sum.elim (fun j => (1 : L v) ⊗ₜ[𝓞] Ψ v (X j))
                (fun j => Algebra.TensorProduct.map (ι v : 𝒮.Et v →ₐ[𝓞] L v) (ι v : 𝒮.Et v →ₐ[𝓞] L v)
                  (c₂ v j)))
              (Φ.toPowerSeries j)))
          (Φ.toPowerSeries i)) :
    ∃ ee : ∀ v, 𝒮.Gc v ⊗[ZMod p] 𝒮.Ge v →ₐc[ZMod p] ZMod p ⊗[𝓞] L v,
      (∀ v, Function.Bijective (ee v)) ∧
      (∀ v (F : MvPowerSeries (Fin 𝒮.d) 𝓞),
        ee v (𝒮.κ v (F.map (algebraMap 𝓞 (ZMod p))) ⊗ₜ[ZMod p] (1 : 𝒮.Ge v)) =
          (1 : ZMod p) ⊗ₜ[𝓞] Ψ v F) ∧
      (∀ v (y : 𝒮.Et v),
        ee v ((1 : 𝒮.Gc v) ⊗ₜ[ZMod p] 𝒮.θe v ((1 : ZMod p) ⊗ₜ[𝓞] y)) = (1 : ZMod p) ⊗ₜ[𝓞] ι v y) ∧
      (∀ v, (ee v).comp (Bialgebra.TensorProduct.map (𝒮.sc v) (𝒮.se v)) =
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (t v)).comp (ee (v + 1))) := by
  classical
  haveI : Nontrivial 𝓞 := (algebraMap 𝓞 (ZMod p)).domain_nontrivial

  let E : ∀ v, 𝒮.Gc v →ₐc[ZMod p] ZMod p ⊗[𝓞] L v := fun v =>
    haveI : IsAdicComplete (Ideal.span {(p : L v ⊗[𝓞] L v)}) (L v ⊗[𝓞] L v) :=
      IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (L v ⊗[𝓞] L v)
    LVd.ee p hker (Ψ v) Φ v (hΨtors v) (𝒮.κ v) (h𝒮.κ_surjective v) 𝒮.Φ₀ hΦ (h𝒮.ker_κ v)
      (ι v) (c₂ v) (h𝒮.κ_X_mem_radical v) (h𝒮.counit_κ_X v) (h𝒮.comul_κ_X v) (hΨε v) (hc₂p v)
      (hcomul v)
  have hE : ∀ v (a : 𝒮.Gc v), E v a =
      LVd.e p hker (Ψ v) Φ v (hΨtors v) (𝒮.κ v) (h𝒮.κ_surjective v) 𝒮.Φ₀ hΦ (h𝒮.ker_κ v) a :=
    fun v a => rfl
  have hEκ : ∀ v (F : MvPowerSeries (Fin 𝒮.d) 𝓞),
      E v (𝒮.κ v (F.map (algebraMap 𝓞 (ZMod p)))) = (1 : ZMod p) ⊗ₜ[𝓞] Ψ v F := fun v F => by
    rw [hE]
    exact LVd.e_κ_red p hker (Ψ v) Φ v (hΨtors v) (𝒮.κ v) (h𝒮.κ_surjective v) 𝒮.Φ₀ hΦ
      (h𝒮.ker_κ v) F

  let EE : ∀ v, 𝒮.Gc v ⊗[ZMod p] 𝒮.Ge v →ₐc[ZMod p] ZMod p ⊗[𝓞] L v := fun v =>
    LVd.eeT p (E v) (ι v) (𝒮.θe v) (h𝒮.θe_bijective v)
  have hEE : ∀ v (a : 𝒮.Gc v) (b : 𝒮.Ge v),
      EE v (a ⊗ₜ[ZMod p] b) = E v a * LVd.eEt p (ι v) (𝒮.θe v) (h𝒮.θe_bijective v) b :=
    fun v a b => LVd.eeT_tmul p (E v) (ι v) (𝒮.θe v) (h𝒮.θe_bijective v) a b
  have hθ : ∀ v (c : ZMod p) (y : 𝒮.Et v),
      LVd.eEt p (ι v) (𝒮.θe v) (h𝒮.θe_bijective v) (𝒮.θe v (c ⊗ₜ[𝓞] y)) = c ⊗ₜ[𝓞] ι v y :=
    fun v c y => LVd.eEt_θe_tmul p (ι v) (𝒮.θe v) (h𝒮.θe_bijective v) c y

  have hκcl : ∀ v (F : MvPowerSeries (Fin 𝒮.d) 𝓞),
      EE v (𝒮.κ v (F.map (algebraMap 𝓞 (ZMod p))) ⊗ₜ[ZMod p] (1 : 𝒮.Ge v)) =
        (1 : ZMod p) ⊗ₜ[𝓞] Ψ v F := fun v F => by
    rw [hEE, hEκ, map_one, mul_one]
  have hθcl : ∀ v (y : 𝒮.Et v),
      EE v ((1 : 𝒮.Gc v) ⊗ₜ[ZMod p] 𝒮.θe v ((1 : ZMod p) ⊗ₜ[𝓞] y)) = (1 : ZMod p) ⊗ₜ[𝓞] ι v y :=
    fun v y => by rw [hEE, map_one, one_mul, hθ]
  refine ⟨EE, fun v => ?_, hκcl, hθcl, fun v => ?_⟩
  ·
    have hsurj : Function.Surjective (EE v) := by
      have key : ∀ (c : ZMod p) (w : 𝒮.Et v ⊗[𝓞] MvPowerSeries (Fin 𝒮.d) 𝓞), ∃ x, EE v x =
          c ⊗ₜ[𝓞] Algebra.TensorProduct.lift (ι v : 𝒮.Et v →ₐ[𝓞] L v) (Ψ v)
            (fun _ _ => Commute.all _ _) w := by
        intro c w
        induction w using TensorProduct.induction_on with
        | zero => exact ⟨0, by rw [map_zero, map_zero, TensorProduct.tmul_zero]⟩
        | tmul y F =>
          refine ⟨c • (𝒮.κ v (F.map (algebraMap 𝓞 (ZMod p))) ⊗ₜ[ZMod p]
            𝒮.θe v ((1 : ZMod p) ⊗ₜ[𝓞] y)), ?_⟩
          rw [map_smul, hEE, hEκ, hθ, Algebra.TensorProduct.lift_tmul, BialgHom.coe_toAlgHom,
            Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm (Ψ v F), TensorProduct.smul_tmul',
            smul_eq_mul, mul_one]
        | add x y hx hy =>
          obtain ⟨a, ha⟩ := hx
          obtain ⟨b, hb⟩ := hy
          exact ⟨a + b, by rw [map_add, ha, hb, map_add, TensorProduct.tmul_add]⟩
      intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | tmul c l =>
        obtain ⟨w, rfl⟩ := hgen v l
        exact key c w
      | add x y hx hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        exact ⟨a + b, map_add _ _ _⟩
    haveI := h𝒮.finite_Gc v
    haveI := h𝒮.finite_Ge v
    have hfin : Module.finrank (ZMod p) (𝒮.Gc v ⊗[ZMod p] 𝒮.Ge v) =
        Module.finrank (ZMod p) (ZMod p ⊗[𝓞] L v) := by
      rw [Module.finrank_tensorProduct, Module.finrank_baseChange, h𝒮.finrank_Gc, h𝒮.finrank_Ge,
        hrankL, ← pow_add, mul_add]
    exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
      (f := (EE v : 𝒮.Gc v ⊗[ZMod p] 𝒮.Ge v →ₐ[ZMod p] ZMod p ⊗[𝓞] L v).toLinearMap)).2 hsurj, hsurj⟩
  ·
    have hleft : ∀ a : 𝒮.Gc (v + 1), E v (𝒮.sc v a) =
        Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (t v) (E (v + 1) a) := by
      intro a
      obtain ⟨F', rfl⟩ := h𝒮.κ_surjective (v + 1) a
      obtain ⟨F, rfl⟩ := LVd.red_surjective p (𝓞 := 𝓞) 𝒮.d F'
      have hsc : 𝒮.sc v (𝒮.κ (v + 1) (LVd.red p 𝒮.d F)) = 𝒮.κ v (LVd.red p 𝒮.d F) := by
        have := AlgHom.congr_fun (h𝒮.sc_comp_κ v) (LVd.red p 𝒮.d F)
        rwa [AlgHom.comp_apply, BialgHom.coe_toAlgHom] at this
      have ht : t v (Ψ (v + 1) F) = Ψ v F := by
        have := AlgHom.congr_fun (hΨt v) F
        rwa [AlgHom.comp_apply, BialgHom.coe_toAlgHom] at this
      rw [hsc, hEκ, hEκ, Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply, ht]
    have hright : ∀ b : 𝒮.Ge (v + 1),
        LVd.eEt p (ι v) (𝒮.θe v) (h𝒮.θe_bijective v) (𝒮.se v b) =
          Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (t v)
            (LVd.eEt p (ι (v + 1)) (𝒮.θe (v + 1)) (h𝒮.θe_bijective (v + 1)) b) := by
      intro b
      obtain ⟨w, rfl⟩ := (h𝒮.θe_bijective (v + 1)).2 b
      induction w using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul c y =>
        have hse : 𝒮.se v (𝒮.θe (v + 1) (c ⊗ₜ[𝓞] y)) = 𝒮.θe v (c ⊗ₜ[𝓞] 𝒮.st v y) := by
          have := DFunLike.congr_fun (h𝒮.θe_comp v) (c ⊗ₜ[𝓞] y)
          rw [BialgHom.comp_apply, BialgHom.comp_apply, Bialgebra.TensorProduct.map_tmul,
            BialgHom.id_apply] at this
          exact this.symm
        have hιt' : t v (ι (v + 1) y) = ι v (𝒮.st v y) := by
          have := DFunLike.congr_fun (hιt v) y
          rwa [BialgHom.comp_apply, BialgHom.comp_apply] at this
        rw [hse, hθ, hθ, Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply, hιt']
      | add x y hx hy => simp only [map_add, hx, hy]
    apply BialgHom.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b =>
      rw [BialgHom.comp_apply, BialgHom.comp_apply, Bialgebra.TensorProduct.map_tmul, hEE, hEE, map_mul,
        hleft, hright]
    | add x y hx hy => simp only [map_add, hx, hy]

end S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle
end P2MW
export P2MW.S_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle (solution)
