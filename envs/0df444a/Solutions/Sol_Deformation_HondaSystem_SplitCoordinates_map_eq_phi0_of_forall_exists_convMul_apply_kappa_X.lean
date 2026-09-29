-- Prove2me | solution 1 for Deformation.HondaSystem.SplitCoordinates.map_eq_phi0_of_forall_exists_convMul_apply_kappa_X
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/830049c9-cf2f-539e-9249-6622a955d19d

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct
open MvPowerSeries

universe u v w

namespace MvFormalGroup
p2m_export "MvFormalGroup" "map mk toPowerSeries adicEval adicEval_mem_radical map_adicEval"
namespace LiftLaw
p2m_open "MvFormalGroup"

open MvPowerSeries MvPowerSeries.WithPiTopology Filter

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

end MvFormalGroup.LiftLaw

namespace MvFormalGroup
p2m_export "MvFormalGroup" "map mk toPowerSeries adicEval adicEval_mem_radical map_adicEval"
namespace LiftLaw
p2m_open "MvFormalGroup"

open MvPowerSeries

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

theorem eq_zero_or_eq_single_of_degree_lt_two {τ : Type*} (d : τ →₀ ℕ) (hd : d.degree < 2) :
    d = 0 ∨ ∃ t, d = Finsupp.single t 1 := by
  classical
  by_cases h0 : d = 0
  · exact Or.inl h0
  obtain ⟨t, ht⟩ := Finsupp.support_nonempty_iff.2 h0
  have ht' : d t ≠ 0 := Finsupp.mem_support_iff.1 ht
  refine Or.inr ⟨t, Finsupp.ext fun s => ?_⟩
  by_cases hs : s = t
  · subst hs
    have := Finsupp.le_degree s d
    rw [Finsupp.single_eq_same]
    omega
  · rw [Finsupp.single_eq_of_ne hs]
    by_contra hds
    have hsub : ({s, t} : Finset τ) ⊆ d.support := by
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact Finsupp.mem_support_iff.2 hds
      · rw [Finset.mem_singleton.1 hi]; exact ht
    have h2 : d s + d t ≤ d.degree := by
      rw [Finsupp.degree_apply, ← Finset.sum_pair hs]
      exact Finset.sum_le_sum_of_subset hsub
    omega

theorem adicEval_bot_eq_of_linear
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {τ σ : Type*} [Fintype τ] [DecidableEq σ]
    (ι : τ → σ) (hι : Function.Injective ι) (v : τ → A)
    (hv : ∀ m : τ →₀ ℕ, 2 ≤ m.degree → m.prod (fun t e => v t ^ e) = 0)
    (w : σ → A) (hwι : ∀ t, w (ι t) = v t) (hw0 : ∀ s, s ∉ Set.range ι → w s = 0)
    (F : MvPowerSeries σ R) :
    adicEval ⊥ w F = algebraMap R A (MvPowerSeries.coeff (0 : σ →₀ ℕ) F)
      + ∑ t, MvPowerSeries.coeff (Finsupp.single (ι t) 1) F • v t := by
  classical

  let T : Finset (σ →₀ ℕ) := insert 0 (Finset.univ.image fun t => Finsupp.single (ι t) 1)
  have hT : ∀ m, m ∉ T → m.prod (fun s e => w s ^ e) = 0 := by
    intro m hm
    by_cases hsupp : ∃ s ∈ m.support, s ∉ Set.range ι
    · obtain ⟨s, hs, hsι⟩ := hsupp
      refine Finset.prod_eq_zero hs ?_
      change w s ^ m s = 0
      rw [hw0 s hsι, zero_pow (Finsupp.mem_support_iff.1 hs)]
    · push Not at hsupp
      have hsub : ↑m.support ⊆ Set.range ι := fun s hs => hsupp s hs
      set m' : τ →₀ ℕ := Finsupp.comapDomain ι m hι.injOn with hm'
      have hmm' : Finsupp.mapDomain ι m' = m := Finsupp.mapDomain_comapDomain ι hι m hsub
      have hprod : m.prod (fun s e => w s ^ e) = m'.prod (fun t e => v t ^ e) := by
        conv_lhs => rw [← hmm']
        rw [Finsupp.prod_mapDomain_index_inj hι]
        exact Finset.prod_congr rfl fun t _ => by simp only [hwι]
      rw [hprod]
      by_cases hdeg : 2 ≤ m'.degree
      · exact hv m' hdeg
      · exfalso
        rcases eq_zero_or_eq_single_of_degree_lt_two m' (not_le.1 hdeg) with h | ⟨t, h⟩
        · apply hm
          rw [← hmm', h, Finsupp.mapDomain_zero]
          exact Finset.mem_insert_self _ _
        · apply hm
          rw [← hmm', h, Finsupp.mapDomain_single]
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ t))

  let q : MvPolynomial σ R := MvPolynomial.C (MvPowerSeries.coeff (0 : σ →₀ ℕ) F) +
    ∑ t, MvPolynomial.C (MvPowerSeries.coeff (Finsupp.single (ι t) 1) F) * MvPolynomial.X (ι t)
  have hq0 : MvPolynomial.coeff 0 q = MvPowerSeries.coeff (0 : σ →₀ ℕ) F := by
    simp only [q, MvPolynomial.coeff_add, MvPolynomial.coeff_C, if_true, MvPolynomial.coeff_sum,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_zero_X, mul_zero, Finset.sum_const_zero, add_zero]
  have hq1 : ∀ t, MvPolynomial.coeff (Finsupp.single (ι t) 1) q =
      MvPowerSeries.coeff (Finsupp.single (ι t) 1) F := by
    intro t
    have hne : (0 : σ →₀ ℕ) ≠ Finsupp.single (ι t) 1 :=
      (Finsupp.single_ne_zero.2 one_ne_zero).symm
    simp only [q, MvPolynomial.coeff_add, MvPolynomial.coeff_C, if_neg hne, zero_add,
      MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X']
    rw [Finset.sum_eq_single t]
    · rw [if_pos rfl, mul_one]
    · intro t' _ ht'
      rw [if_neg, mul_zero]
      intro h
      exact ht' (hι ((Finsupp.single_left_inj one_ne_zero).1 h))
    · intro h; exact absurd (Finset.mem_univ t) h
  have hq : ∀ m ∈ T, MvPolynomial.coeff m q = MvPowerSeries.coeff m F := by
    intro m hm
    rcases Finset.mem_insert.1 hm with rfl | hm
    · exact hq0
    · obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hm
      exact hq1 t
  rw [adicEval_eq_aeval_of_forall_prod_eq_zero ⊥ inferInstance w F q T hT hq]
  simp only [q, map_add, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, hwι,
    Algebra.smul_def]

end Packaged

end MvFormalGroup.LiftLaw

namespace MvFormalGroup
p2m_export "MvFormalGroup" "map mk toPowerSeries adicEval adicEval_mem_radical map_adicEval"
namespace LiftLaw
p2m_open "MvFormalGroup"

theorem mem_radical_bot_of_isNilpotent {S : Type*} [CommSemiring S] {x : S} (hx : IsNilpotent x) :
    x ∈ (⊥ : Ideal S).radical := by
  obtain ⟨n, hn⟩ := hx
  exact ⟨n, by rw [hn]; exact Submodule.zero_mem _⟩

end MvFormalGroup.LiftLaw

open MvPowerSeries

noncomputable section

namespace MvFormalGroup
p2m_export "MvFormalGroup" "map mk toPowerSeries adicEval adicEval_mem_radical map_adicEval"
namespace LiftLaw
namespace NaturalLaw
p2m_open "MvFormalGroup"

section Trunc

variable (σ : Type*) (R : Type*) [CommRing R]

def truncIdeal (N : ℕ) : Ideal (MvPolynomial σ R) where
  carrier := {f | ∀ m : σ →₀ ℕ, m.degree < N → MvPolynomial.coeff m f = 0}
  zero_mem' := fun m _ => MvPolynomial.coeff_zero m
  add_mem' := fun {f g} hf hg m hm => by
    rw [MvPolynomial.coeff_add, hf m hm, hg m hm, add_zero]
  smul_mem' := fun h f hf m hm => by
    classical
    rw [smul_eq_mul, MvPolynomial.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have hle : x.2.degree ≤ m.degree := by
      rw [← hx, map_add]
      exact le_add_self
    rw [hf x.2 (lt_of_le_of_lt hle hm), mul_zero]

abbrev TruncAlg (N : ℕ) : Type _ := MvPolynomial σ R ⧸ truncIdeal σ R N

def DegLT (N : ℕ) : Type _ := {m : σ →₀ ℕ // m.degree < N}

scoped instance instFiniteDegLT [Finite σ] (N : ℕ) : Finite (DegLT σ N) :=
  (Finsupp.finite_of_degree_lt (σ := σ) N).to_subtype

variable {σ R}

theorem mem_truncIdeal {N : ℕ} {f : MvPolynomial σ R} :
    f ∈ truncIdeal σ R N ↔ ∀ m : σ →₀ ℕ, m.degree < N → MvPolynomial.coeff m f = 0 :=
  Iff.rfl

def coeffsLT (N : ℕ) : MvPolynomial σ R →ₗ[R] (DegLT σ N → R) where
  toFun f m := MvPolynomial.coeff m.1 f
  map_add' f g := by
    funext m
    exact MvPolynomial.coeff_add m.1 f g
  map_smul' r f := by
    funext m
    rw [RingHom.id_apply, Pi.smul_apply, MvPolynomial.coeff_smul]

theorem coeffsLT_apply (N : ℕ) (f : MvPolynomial σ R) (m : DegLT σ N) :
    coeffsLT N f m = MvPolynomial.coeff m.1 f :=
  rfl

theorem ker_coeffsLT (N : ℕ) :
    LinearMap.ker (coeffsLT (σ := σ) (R := R) N) = (truncIdeal σ R N).restrictScalars R := by
  ext f
  rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, mem_truncIdeal]
  constructor
  · intro h m hm
    exact congrFun h ⟨m, hm⟩
  · intro h
    funext m
    exact h m.1 m.2

theorem coeffsLT_surjective [Finite σ] (N : ℕ) :
    Function.Surjective (coeffsLT (σ := σ) (R := R) N) := by
  classical
  haveI := Fintype.ofFinite (DegLT σ N)
  intro c
  refine ⟨∑ n : DegLT σ N, MvPolynomial.monomial n.1 (c n), ?_⟩
  funext m
  rw [coeffsLT_apply, MvPolynomial.coeff_sum, Finset.sum_eq_single m]
  · rw [MvPolynomial.coeff_monomial, if_pos rfl]
  · intro n _ hnm
    rw [MvPolynomial.coeff_monomial, if_neg fun h => hnm (Subtype.ext h)]
  · intro h
    exact absurd (Finset.mem_univ m) h

private def coordAux₁ [Finite σ] (N : ℕ) :=
  LinearMap.quotKerEquivOfSurjective (coeffsLT (σ := σ) (R := R) N) (coeffsLT_surjective N)

private def coordAux₂ (N : ℕ) :=
  Submodule.quotEquivOfEq _ _ (ker_coeffsLT (σ := σ) (R := R) N).symm

private def coordAux₃ (N : ℕ) :=
  (Submodule.Quotient.restrictScalarsEquiv R (truncIdeal σ R N)).symm

private def coordAux₂₁ [Finite σ] (N : ℕ) := (coordAux₂ (σ := σ) (R := R) N) ≪≫ₗ (coordAux₁ N)

variable (σ R) in

def coord [Finite σ] (N : ℕ) : TruncAlg σ R N ≃ₗ[R] (DegLT σ N → R) :=
  (coordAux₃ (σ := σ) (R := R) N) ≪≫ₗ (coordAux₂₁ N)

theorem coord_mk [Finite σ] (N : ℕ) (f : MvPolynomial σ R) (m : DegLT σ N) :
    coord σ R N (Ideal.Quotient.mk (truncIdeal σ R N) f) m = MvPolynomial.coeff m.1 f :=
  rfl

scoped instance instFree [Finite σ] (N : ℕ) : Module.Free R (TruncAlg σ R N) :=
  Module.Free.of_equiv (coord σ R N).symm

scoped instance instFinite [Finite σ] (N : ℕ) : Module.Finite R (TruncAlg σ R N) :=
  Module.Finite.equiv (coord σ R N).symm

variable (R) in

abbrev tX (N : ℕ) (s : σ) : TruncAlg σ R N := Ideal.Quotient.mk _ (MvPolynomial.X s)

theorem mk_eq_mk_iff {N : ℕ} {f g : MvPolynomial σ R} :
    Ideal.Quotient.mk (truncIdeal σ R N) f = Ideal.Quotient.mk _ g ↔
      ∀ m : σ →₀ ℕ, m.degree < N → MvPolynomial.coeff m f = MvPolynomial.coeff m g := by
  rw [Ideal.Quotient.eq, mem_truncIdeal]
  simp only [MvPolynomial.coeff_sub, sub_eq_zero]

theorem monomial_mem_truncIdeal {N : ℕ} {m : σ →₀ ℕ} (hm : N ≤ m.degree) (r : R) :
    MvPolynomial.monomial m r ∈ truncIdeal σ R N := fun n hn => by
  classical
  rw [MvPolynomial.coeff_monomial, if_neg]
  rintro rfl
  exact absurd hm (not_le.2 hn)

theorem prod_tX_pow_eq_zero {N : ℕ} {m : σ →₀ ℕ} (hm : N ≤ m.degree) :
    m.prod (fun s e => (tX R N s) ^ e) = 0 := by
  have h : m.prod (fun s e => (tX R N s) ^ e) =
      Ideal.Quotient.mk _ (m.prod fun s e => (MvPolynomial.X s : MvPolynomial σ R) ^ e) := by
    rw [map_finsuppProd]
    simp only [map_pow]
  rw [h, Finsupp.prod, MvPolynomial.prod_X_pow_eq_monomial, Ideal.Quotient.eq_zero_iff_mem]
  exact monomial_mem_truncIdeal hm 1

theorem isNilpotent_tX (N : ℕ) (s : σ) : IsNilpotent (tX R N s) := by
  refine ⟨N, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.X_pow_eq_monomial]
  exact monomial_mem_truncIdeal (le_of_eq (Finsupp.degree_single _ _).symm) 1

theorem aeval_tX (N : ℕ) (f : MvPolynomial σ R) :
    MvPolynomial.aeval (tX R N) f = Ideal.Quotient.mk (truncIdeal σ R N) f := by
  have h := MvPolynomial.comp_aeval (MvPolynomial.X (R := R) (σ := σ))
    (Ideal.Quotient.mkₐ R (truncIdeal σ R N))
  rw [MvPolynomial.aeval_X_left, AlgHom.comp_id] at h
  exact (DFunLike.congr_fun h f).symm

variable {S : Type*} [CommRing S] [Algebra R S]

theorem aeval_eq_zero_of_mem_truncIdeal {N : ℕ} {w : σ → S}
    (hw : ∀ m : σ →₀ ℕ, N ≤ m.degree → m.prod (fun s e => w s ^ e) = 0)
    {f : MvPolynomial σ R} (hf : f ∈ truncIdeal σ R N) : MvPolynomial.aeval w f = 0 := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases hm : m.degree < N
  · rw [hf m hm, map_zero, zero_mul]
  · rw [show (∏ i ∈ m.support, w i ^ m i) = m.prod (fun s e => w s ^ e) from rfl,
      hw m (not_lt.1 hm), mul_zero]

private noncomputable def _root_.MvFormalGroup.LiftLaw.NaturalLaw.lift (N : ℕ) (w : σ → S)
    (hw : ∀ m : σ →₀ ℕ, N ≤ m.degree → m.prod (fun s e => w s ^ e) = 0) :
    TruncAlg σ R N →ₐ[R] S :=
  Ideal.Quotient.liftₐ (truncIdeal σ R N) (MvPolynomial.aeval w)
    (fun _ hf => aeval_eq_zero_of_mem_truncIdeal hw hf)

p2m_export "MvFormalGroup.LiftLaw.NaturalLaw" "lift"
theorem lift_mk (N : ℕ) (w : σ → S)
    (hw : ∀ m : σ →₀ ℕ, N ≤ m.degree → m.prod (fun s e => w s ^ e) = 0) (f : MvPolynomial σ R) :
    lift N w hw (Ideal.Quotient.mk _ f) = MvPolynomial.aeval w f :=
  rfl

theorem lift_tX (N : ℕ) (w : σ → S)
    (hw : ∀ m : σ →₀ ℕ, N ≤ m.degree → m.prod (fun s e => w s ^ e) = 0) (s : σ) :
    lift N w hw (tX R N s) = w s := by
  rw [lift_mk, MvPolynomial.aeval_X]

theorem read_linear [Fintype σ] [DecidableEq σ] (c₀ : R) (c : σ → R) (i : σ)
    (h : algebraMap R (TruncAlg σ R 2) c₀ + ∑ j, c j • tX R 2 j = tX R 2 i) :
    c₀ = 0 ∧ ∀ j, c j = if i = j then 1 else 0 := by
  have h0 : Finsupp.degree (0 : σ →₀ ℕ) < 2 := by rw [map_zero]; exact two_pos
  have h1 : ∀ j : σ, (Finsupp.single j 1).degree < 2 := fun j => by
    rw [Finsupp.degree_single]; exact one_lt_two
  have halg : algebraMap R (TruncAlg σ R 2) c₀ = Ideal.Quotient.mk _ (MvPolynomial.C c₀) := rfl
  have key : ∀ m : DegLT σ 2, coord σ R 2 (algebraMap R (TruncAlg σ R 2) c₀ + ∑ j, c j • tX R 2 j) m =
      coord σ R 2 (tX R 2 i) m := fun m => by rw [h]
  simp only [map_add, map_sum, map_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, halg, coord_mk] at key
  constructor
  · have k := key ⟨0, h0⟩
    simp only [MvPolynomial.coeff_C, MvPolynomial.coeff_X', if_true] at k
    simpa [Finsupp.single_eq_zero] using k
  · intro j
    have k := key ⟨Finsupp.single j 1, h1 j⟩
    simp only [MvPolynomial.coeff_C, MvPolynomial.coeff_X', Finsupp.single_left_inj one_ne_zero,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at k
    simpa [eq_comm, Ne.symm (Finsupp.single_ne_zero.2 one_ne_zero)] using k

end Trunc

end MvFormalGroup.LiftLaw.NaturalLaw
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw"
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup"

end
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"

noncomputable section

namespace MvFormalGroup
p2m_export "MvFormalGroup" "map mk toPowerSeries adicEval adicEval_mem_radical map_adicEval"
namespace LiftLaw
namespace NaturalLaw
p2m_open "MvFormalGroup"

section BotEval

variable {σ : Type*} {R : Type*} [CommRing R]

theorem mem_radical_of_isNilpotent {S : Type*} [CommSemiring S] {I : Ideal S} {x : S}
    (hx : IsNilpotent x) : x ∈ I.radical := by
  obtain ⟨n, hn⟩ := hx
  exact ⟨n, by rw [hn]; exact I.zero_mem⟩

theorem isNilpotent_of_mem_radical_bot {S : Type*} [CommSemiring S] {x : S}
    (hx : x ∈ (⊥ : Ideal S).radical) : IsNilpotent x := by
  obtain ⟨n, hn⟩ := hx
  exact ⟨n, (Ideal.mem_bot).1 hn⟩

theorem isNilpotent_adicEval_bot {S : Type*} [CommRing S] [Algebra R S] [Finite σ] {w : σ → S}
    (hw : ∀ s, IsNilpotent (w s)) {F : MvPowerSeries σ R} (hF : F.constantCoeff = 0) :
    IsNilpotent (adicEval ⊥ w F) :=
  isNilpotent_of_mem_radical_bot
    (adicEval_mem_radical ⊥ (fun s => mem_radical_of_isNilpotent (hw s)) hF)

def truncPoly [Finite σ] (N : ℕ) (F : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ n ∈ (Finsupp.finite_of_degree_lt (σ := σ) N).toFinset,
    MvPolynomial.monomial n (MvPowerSeries.coeff n F)

theorem coeff_truncPoly [Finite σ] {N : ℕ} (F : MvPowerSeries σ R) {m : σ →₀ ℕ}
    (hm : m.degree < N) : MvPolynomial.coeff m (truncPoly N F) = MvPowerSeries.coeff m F := by
  classical
  rw [truncPoly, MvPolynomial.coeff_sum, Finset.sum_eq_single m]
  · rw [MvPolynomial.coeff_monomial, if_pos rfl]
  · intro n _ hnm
    rw [MvPolynomial.coeff_monomial, if_neg hnm]
  · intro h
    exact absurd ((Set.Finite.mem_toFinset (Finsupp.finite_of_degree_lt N)).2 hm) h

theorem adicEval_bot_tX [Finite σ] (N : ℕ) (F : MvPowerSeries σ R) :
    adicEval ⊥ (tX R N) F = Ideal.Quotient.mk (truncIdeal σ R N) (truncPoly N F) := by
  rw [← aeval_tX]
  exact adicEval_eq_aeval_of_degree ⊥ inferInstance (tX R N) F (truncPoly N F) N
    (fun m hm => prod_tX_pow_eq_zero hm) (fun m hm => coeff_truncPoly F hm)

theorem coord_adicEval_bot_tX [Finite σ] (N : ℕ) (F : MvPowerSeries σ R) (m : DegLT σ N) :
    coord σ R N (adicEval ⊥ (tX R N) F) m = MvPowerSeries.coeff m.1 F := by
  rw [adicEval_bot_tX, coord_mk, coeff_truncPoly F m.2]

theorem eq_of_forall_adicEval_bot_tX_eq [Finite σ] {F G : MvPowerSeries σ R}
    (h : ∀ N : ℕ, adicEval ⊥ (tX R N) F = adicEval ⊥ (tX R N) G) : F = G := by
  ext m
  have := congrArg (fun z => coord σ R (m.degree + 1) z ⟨m, Nat.lt_succ_self _⟩) (h (m.degree + 1))
  simpa only [coord_adicEval_bot_tX] using this

end BotEval
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"

end MvFormalGroup.LiftLaw.NaturalLaw
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"

end
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"

noncomputable section
noncomputable section

namespace MvFormalGroup
p2m_export "MvFormalGroup" "map mk toPowerSeries adicEval adicEval_mem_radical map_adicEval"
namespace LiftLaw
namespace NaturalLaw
p2m_open "MvFormalGroup"

section Construction

variable (𝓞 : Type u) [CommRing 𝓞] (d : ℕ)

abbrev testAlg (N : ℕ) : Type u := TruncAlg (Fin d ⊕ Fin d) 𝓞 N

def genX (N : ℕ) : Fin d → testAlg 𝓞 d N := fun j => tX 𝓞 N (Sum.inl j)

def genY (N : ℕ) : Fin d → testAlg 𝓞 d N := fun j => tX 𝓞 N (Sum.inr j)

theorem sumElim_genX_genY (N : ℕ) : Sum.elim (genX 𝓞 d N) (genY 𝓞 d N) = tX 𝓞 N := by
  funext s
  rcases s with j | j <;> rfl

theorem isNilpotent_genX (N : ℕ) (j : Fin d) : IsNilpotent (genX 𝓞 d N j) := isNilpotent_tX N _

theorem isNilpotent_genY (N : ℕ) (j : Fin d) : IsNilpotent (genY 𝓞 d N j) := isNilpotent_tX N _

end Construction
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"

end MvFormalGroup.LiftLaw.NaturalLaw
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"

end
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"

namespace MvFormalGroup
p2m_export "MvFormalGroup" "map mk toPowerSeries adicEval adicEval_mem_radical map_adicEval"
namespace LiftLaw
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

end MvFormalGroup.LiftLaw
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"

namespace MvFormalGroup
p2m_export "MvFormalGroup" "map mk toPowerSeries adicEval adicEval_mem_radical map_adicEval"
namespace LiftLaw
p2m_open "MvFormalGroup"

variable {g : ℕ} {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

theorem toPowerSeries_injective' :
    Function.Injective (MvFormalGroup.toPowerSeries : MvFormalGroup g R → _) := by
  rintro ⟨a, _, _, _, _⟩ ⟨b, _, _, _, _⟩ h
  congr

end MvFormalGroup.LiftLaw
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"

namespace MvFormalGroup
p2m_export "MvFormalGroup" "map mk toPowerSeries adicEval adicEval_mem_radical map_adicEval"
namespace LiftLaw
namespace NaturalLaw
p2m_open "MvFormalGroup"

open scoped TensorProduct

section TruncBaseChange

variable (𝓞 : Type*) [CommRing 𝓞] (k : Type*) [CommRing k] [Algebra 𝓞 k] (σ : Type*) [Finite σ]

noncomputable def truncBaseChange (N : ℕ) : k ⊗[𝓞] TruncAlg σ 𝓞 N →ₐ[k] TruncAlg σ k N :=
  Algebra.TensorProduct.lift (Algebra.ofId k (TruncAlg σ k N))
    (lift N (tX k N) fun _ hm => prod_tX_pow_eq_zero hm)
    (fun _ _ => @Commute.all (TruncAlg σ k N) _ _ _)

theorem truncBaseChange_one_tmul_tX (N : ℕ) (s : σ) :
    truncBaseChange 𝓞 k σ N ((1 : k) ⊗ₜ[𝓞] tX 𝓞 N s) = tX k N s := by
  rw [truncBaseChange, Algebra.TensorProduct.lift_tmul, map_one, one_mul, lift_tX]

end TruncBaseChange
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"

end MvFormalGroup.LiftLaw.NaturalLaw
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"

namespace Deformation
p2m_export "Deformation" "HondaSystem DieudonneModule HondaSystem.SplitCoordinates"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk L SplitCoordinates"
namespace LiftLaw
p2m_open "Deformation.HondaSystem Deformation"

open scoped TensorProduct
open MvPowerSeries MvFormalGroup.LiftLaw MvFormalGroup.LiftLaw.NaturalLaw

section LiftB

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
  {r : ℕ} {H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞)}
  {G : ℕ → Type v} [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
  {s : ∀ v, G (v + 1) →ₐc[ZMod p] G v}
  {π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v)}
  (𝒮 : SplitCoordinates p r H₁ G s π)

theorem span_natCast_eq_bot (A : Type*) [CommRing A] [Algebra (ZMod p) A] :
    Ideal.span {(p : A)} = ⊥ := by
  rw [Ideal.span_singleton_eq_bot, ← map_natCast (algebraMap (ZMod p) A), ZMod.natCast_self, map_zero]

theorem adicEval_tX_map_eq_of_convMul [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (hℒ : 𝒮.Lawful) (Φ : MvFormalGroup 𝒮.d 𝓞) (N : ℕ)
    (g : Type*) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g]
    (xy : Fin 𝒮.d ⊕ Fin 𝒮.d → g) (hxy : ∀ t, IsNilpotent (xy t))
    (T : Type*) [CommRing T] [Algebra 𝓞 T] [Algebra (ZMod p) T] [IsScalarTower 𝓞 (ZMod p) T]
    (φ : g →ₐ[𝓞] T)
    (ρ : T →ₐ[ZMod p] TruncAlg (Fin 𝒮.d ⊕ Fin 𝒮.d) (ZMod p) N)
    (hρ : ∀ t, ρ (φ (xy t)) = tX (ZMod p) N t)
    {v : ℕ} (fx fy fw : 𝒮.Gc v →ₐ[ZMod p] T)
    (hx : ∀ j, fx (𝒮.κ v (X j)) = φ (xy (Sum.inl j)))
    (hy : ∀ j, fy (𝒮.κ v (X j)) = φ (xy (Sum.inr j)))
    (hw : ∀ i, fw (𝒮.κ v (X i)) =
      φ (MvFormalGroup.adicEval (Ideal.span {(p : g)}) xy (Φ.toPowerSeries i)))
    (hconv : fw = (WithConv.toConv fx * WithConv.toConv fy).ofConv) (i : Fin 𝒮.d) :
    MvFormalGroup.adicEval ⊥ (tX (ZMod p) N) ((Φ.map (algebraMap 𝓞 (ZMod p))).toPowerSeries i) =
      MvFormalGroup.adicEval ⊥ (tX (ZMod p) N) (𝒮.Φ₀.toPowerSeries i) := by
  classical
  let pt : Fin 𝒮.d ⊕ Fin 𝒮.d → T := fun t => φ (xy t)
  have hpt_nil : ∀ t, IsNilpotent (pt t) := fun t => (hxy t).map φ
  have hpt_rad : ∀ t, pt t ∈ (⊥ : Ideal T).radical := fun t =>
    MvFormalGroup.LiftLaw.mem_radical_bot_of_isNilpotent (hpt_nil t)

  have hL : fw (𝒮.κ v (X i)) =
      MvFormalGroup.adicEval ⊥ pt ((Φ.map (algebraMap 𝓞 (ZMod p))).toPowerSeries i) := by
    rw [hw i, MvFormalGroup.LiftLaw.adicEval_span_natCast_eq_adicEval_bot_of_isNilpotent (𝓞 := 𝓞) p hxy]
    have h1 := MvFormalGroup.map_adicEval (⊥ : Ideal g) (⊥ : Ideal T) φ Submodule.fg_bot
      (fun x hx => by rw [(Submodule.mem_bot _).1 hx, map_zero]; exact zero_mem _)
      (fun t => MvFormalGroup.LiftLaw.mem_radical_bot_of_isNilpotent (hxy t)) (Φ.toPowerSeries i)
    rw [h1]
    show _ = MvFormalGroup.adicEval ⊥ pt (MvPowerSeries.map (algebraMap 𝓞 (ZMod p)) (Φ.toPowerSeries i))
    rw [MvFormalGroup.LiftLaw.adicEval_bot_map_algebraMap hpt_nil]

  have hκnil : ∀ j, IsNilpotent (𝒮.κ v (X j)) := fun j =>
    isNilpotent_of_mem_radical_bot (by
      have h := hℒ.κ_X_mem_radical v j
      rwa [span_natCast_eq_bot p (𝒮.Gc v)] at h)
  have hR : (WithConv.toConv fx * WithConv.toConv fy).ofConv (𝒮.κ v (X i)) =
      MvFormalGroup.adicEval ⊥ pt (𝒮.Φ₀.toPowerSeries i) := by
    rw [AlgHom.convMul_apply]
    change Algebra.TensorProduct.lift fx fy _ (Coalgebra.comul (R := ZMod p) (𝒮.κ v (X i))) = _
    rw [hℒ.comul_κ_X v i, span_natCast_eq_bot p (𝒮.Gc v ⊗[ZMod p] 𝒮.Gc v)]
    rw [MvFormalGroup.map_adicEval (⊥ : Ideal (𝒮.Gc v ⊗[ZMod p] 𝒮.Gc v)) (⊥ : Ideal T)
      (Algebra.TensorProduct.lift fx fy _) Submodule.fg_bot
      (fun x hx => by rw [(Submodule.mem_bot _).1 hx, map_zero]; exact zero_mem _)
      (by
        rintro (j | j)
        · exact MvFormalGroup.LiftLaw.mem_radical_bot_of_isNilpotent
            ((hκnil j).map (Algebra.TensorProduct.includeLeft :
              𝒮.Gc v →ₐ[ZMod p] 𝒮.Gc v ⊗[ZMod p] 𝒮.Gc v))
        · exact MvFormalGroup.LiftLaw.mem_radical_bot_of_isNilpotent
            ((hκnil j).map (Algebra.TensorProduct.includeRight :
              𝒮.Gc v →ₐ[ZMod p] 𝒮.Gc v ⊗[ZMod p] 𝒮.Gc v)))]
    congr 1
    funext t
    rcases t with j | j
    · simp only [Sum.elim_inl, Algebra.TensorProduct.lift_tmul, map_one, mul_one, hx j]
      rfl
    · simp only [Sum.elim_inr, Algebra.TensorProduct.lift_tmul, map_one, one_mul, hy j]
      rfl

  have key : MvFormalGroup.adicEval ⊥ pt ((Φ.map (algebraMap 𝓞 (ZMod p))).toPowerSeries i) =
      MvFormalGroup.adicEval ⊥ pt (𝒮.Φ₀.toPowerSeries i) := by
    rw [← hL, ← hR, hconv]
  have hρ' := fun F : MvPowerSeries (Fin 𝒮.d ⊕ Fin 𝒮.d) (ZMod p) =>
    MvFormalGroup.map_adicEval (⊥ : Ideal T) (⊥ : Ideal (TruncAlg (Fin 𝒮.d ⊕ Fin 𝒮.d) (ZMod p) N))
      ρ Submodule.fg_bot
      (fun x hx => by rw [(Submodule.mem_bot _).1 hx, map_zero]; exact zero_mem _) hpt_rad F
  have hρpt : (fun t => ρ (pt t)) = tX (ZMod p) N := funext fun t => hρ t
  have := congrArg ρ key
  rwa [hρ', hρ', hρpt] at this

end LiftB
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"

end Deformation.HondaSystem.LiftLaw
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"
p2m_reactivate "P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X.MvFormalGroup.LiftLaw.NaturalLaw"

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v)
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v))
    (𝒮 : Deformation.HondaSystem.SplitCoordinates p r H₁ G s π) (hℒ : 𝒮.Lawful)
    (Φ : MvFormalGroup 𝒮.d 𝓞)
    (hΦ : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
      (x y : Fin 𝒮.d → g), (∀ j, IsNilpotent (x j)) → (∀ j, IsNilpotent (y j)) →
      ∃ (v : ℕ) (fx fy : 𝒮.Gc v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g),
        (∀ j, fx (𝒮.κ v (X j)) = (1 : ZMod p) ⊗ₜ[𝓞] x j) ∧
        (∀ j, fy (𝒮.κ v (X j)) = (1 : ZMod p) ⊗ₜ[𝓞] y j) ∧
        ∀ i, (WithConv.toConv fx * WithConv.toConv fy).ofConv (𝒮.κ v (X i)) =
          (1 : ZMod p) ⊗ₜ[𝓞] MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim x y) (Φ.toPowerSeries i)) :
    Φ.map (algebraMap 𝓞 (ZMod p)) = 𝒮.Φ₀ := by
  classical

  have hgen : ∀ (N : ℕ) (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
      (xy : Fin 𝒮.d ⊕ Fin 𝒮.d → g) (hxy : ∀ t, IsNilpotent (xy t))
      (ρ : TensorProduct 𝓞 (ZMod p) g →ₐ[ZMod p]
        MvFormalGroup.LiftLaw.NaturalLaw.TruncAlg (Fin 𝒮.d ⊕ Fin 𝒮.d) (ZMod p) N)
      (hρ : ∀ t, ρ ((1 : ZMod p) ⊗ₜ[𝓞] xy t) = MvFormalGroup.LiftLaw.NaturalLaw.tX (ZMod p) N t) (i : Fin 𝒮.d),
      MvFormalGroup.adicEval ⊥ (MvFormalGroup.LiftLaw.NaturalLaw.tX (ZMod p) N)
          ((Φ.map (algebraMap 𝓞 (ZMod p))).toPowerSeries i) =
        MvFormalGroup.adicEval ⊥ (MvFormalGroup.LiftLaw.NaturalLaw.tX (ZMod p) N) (𝒮.Φ₀.toPowerSeries i) := by
    intro N g _ _ _ _ xy hxy ρ hρ i
    have hse : Sum.elim (fun j => xy (Sum.inl j)) (fun j => xy (Sum.inr j)) = xy :=
      funext fun t => by rcases t with j | j <;> rfl
    obtain ⟨v, fx, fy, hfx, hfy, hw⟩ := hΦ g (fun j => xy (Sum.inl j)) (fun j => xy (Sum.inr j))
      (fun j => hxy _) (fun j => hxy _)
    refine Deformation.HondaSystem.LiftLaw.adicEval_tX_map_eq_of_convMul p 𝒮 hℒ Φ N g xy hxy
      (TensorProduct 𝓞 (ZMod p) g) Algebra.TensorProduct.includeRight ρ hρ fx fy _ hfx hfy (fun j => ?_) rfl i
    rw [hw j, hse, Algebra.TensorProduct.includeRight_apply]
  apply MvFormalGroup.LiftLaw.toPowerSeries_injective'
  funext i
  refine MvFormalGroup.LiftLaw.NaturalLaw.eq_of_forall_adicEval_bot_tX_eq (R := ZMod p) fun N => ?_
  exact hgen N (MvFormalGroup.LiftLaw.NaturalLaw.testAlg 𝓞 𝒮.d N) (MvFormalGroup.LiftLaw.NaturalLaw.tX 𝓞 N)
    (MvFormalGroup.LiftLaw.NaturalLaw.isNilpotent_tX N)
    (MvFormalGroup.LiftLaw.NaturalLaw.truncBaseChange 𝓞 (ZMod p) (Fin 𝒮.d ⊕ Fin 𝒮.d) N)
    (MvFormalGroup.LiftLaw.NaturalLaw.truncBaseChange_one_tmul_tX 𝓞 (ZMod p) (Fin 𝒮.d ⊕ Fin 𝒮.d) N) i

end
end S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X
end P2MW
export P2MW.S_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X (solution)
