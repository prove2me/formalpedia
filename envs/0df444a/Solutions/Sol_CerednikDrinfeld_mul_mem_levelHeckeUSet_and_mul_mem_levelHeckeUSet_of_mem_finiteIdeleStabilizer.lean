-- Prove2me | solution 1 for CerednikDrinfeld.mul_mem_levelHeckeUSet_and_mul_mem_levelHeckeUSet_of_mem_finiteIdeleStabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/76496992-1679-5339-8305-17fa38689cd0

import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_Submodule_FiniteAdeleBox
import Theorems.Thm_Submodule_finiteAdeleBox_conjByFiniteIdele
import Theorems.Thm_Submodule_conjByFiniteIdele_mul_eq_of_mem_finiteIdeleStabilizer
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_mul_mem_levelHeckeUSet_and_mul_mem_levelHeckeUSet_of_mem_finiteIdeleStabilizer

set_option autoImplicit false

open scoped TensorProduct
open IsDedekindDomain NumberField

noncomputable section

namespace AdelicSlice

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "HOS" => HeightOneSpectrum (𝓞 ℚ)

def s1_Zhat : Subring 𝔸f where
  carrier := {a | ∀ v : HOS, a v ∈ v.adicCompletionIntegers ℚ}
  mul_mem' := fun {a b} ha hb v => by
    show (a * b) v ∈ _
    have : (a * b) v = a v * b v := rfl
    rw [this]; exact mul_mem (ha v) (hb v)
  one_mem' := fun v => by
    have : (1 : 𝔸f) v = 1 := rfl
    rw [this]; exact one_mem _
  add_mem' := fun {a b} ha hb v => by
    have : (a + b) v = a v + b v := rfl
    rw [this]; exact add_mem (ha v) (hb v)
  zero_mem' := fun v => by
    have : (0 : 𝔸f) v = 0 := rfl
    rw [this]; exact zero_mem _
  neg_mem' := fun {a} ha v => by
    have : (-a) v = -(a v) := rfl
    rw [this]; exact neg_mem (ha v)

theorem s1_mem_Zhat_iff (a : 𝔸f) : a ∈ s1_Zhat ↔ ∀ v : HOS, a v ∈ v.adicCompletionIntegers ℚ :=
  Iff.rfl

theorem s1_valued_algebraMap_apply (q : ℚ) (v : HOS) :
    Valued.v ((algebraMap ℚ 𝔸f q) v) = v.valuation ℚ q := by
  have h : (algebraMap ℚ 𝔸f q) v = ((WithVal.equiv (v.valuation ℚ)).symm q : v.adicCompletion ℚ) := rfl
  rw [h]
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v q

theorem s1_algebraMap_apply_mem_integers_iff (q : ℚ) (v : HOS) :
    (algebraMap ℚ 𝔸f q) v ∈ v.adicCompletionIntegers ℚ ↔ v.valuation ℚ q ≤ 1 := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, s1_valued_algebraMap_apply]

theorem s1_valuation_intCast_le_one (v : HOS) (m : ℤ) : v.valuation ℚ (m : ℚ) ≤ 1 := by
  have h : v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ (m : 𝓞 ℚ)) ≤ 1 :=
    IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := ℚ) v (m : 𝓞 ℚ)
  rwa [map_intCast] at h

theorem s1_valuation_natCast_le_one (v : HOS) (n : ℕ) : v.valuation ℚ (n : ℚ) ≤ 1 := by
  have h := s1_valuation_intCast_le_one v (n : ℤ)
  rwa [Int.cast_natCast] at h

theorem s1_algebraMap_intCast_mem_Zhat (m : ℤ) : algebraMap ℚ 𝔸f (m : ℚ) ∈ s1_Zhat := fun v =>
  (s1_algebraMap_apply_mem_integers_iff _ v).mpr (s1_valuation_intCast_le_one v m)

theorem s1_exists_intCast_eq (r : 𝓞 ℚ) : ∃ m : ℤ, ((r : ℚ)) = (m : ℚ) := by
  refine ⟨Rat.ringOfIntegersEquiv r, ?_⟩
  have h0 := Rat.ringOfIntegersEquiv.symm_apply_apply r
  rw [eq_intCast Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv r)] at h0
  calc (r : ℚ) = algebraMap (𝓞 ℚ) ℚ r := rfl
    _ = algebraMap (𝓞 ℚ) ℚ ((Rat.ringOfIntegersEquiv r : ℤ) : 𝓞 ℚ) := by rw [h0]
    _ = ((Rat.ringOfIntegersEquiv r : ℤ) : ℚ) := map_intCast _ _

theorem s1_exists_intCast_of_forall_valuation_le_one (q : ℚ)
    (h : ∀ v : HOS, v.valuation ℚ q ≤ 1) : ∃ m : ℤ, q = (m : ℚ) := by
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ q h
  obtain ⟨m, hm⟩ := s1_exists_intCast_eq r
  refine ⟨m, ?_⟩
  rw [← hm]
  exact hr.symm

section BoxGen

variable {K : Type*} [Ring K] [Algebra ℚ K]

theorem s1_tmul_mem_finiteAdeleBox {Λ : Submodule ℤ K} {z : K} (hz : z ∈ Λ) {a : 𝔸f}
    (ha : a ∈ s1_Zhat) : z ⊗ₜ[ℚ] a ∈ Submodule.finiteAdeleBox Λ :=
  AddSubgroup.subset_closure ⟨z, hz, a, ha, rfl⟩

theorem s1_finiteAdeleBox_le_iff {Λ : Submodule ℤ K} {H : AddSubgroup (K ⊗[ℚ] 𝔸f)} :
    Submodule.finiteAdeleBox Λ ≤ H ↔ ∀ z ∈ Λ, ∀ a : 𝔸f, a ∈ s1_Zhat → z ⊗ₜ[ℚ] a ∈ H := by
  unfold Submodule.finiteAdeleBox
  rw [AddSubgroup.closure_le]
  constructor
  · intro h z hz a ha
    exact h ⟨z, hz, a, ha, rfl⟩
  · rintro h x ⟨z, hz, a, ha, rfl⟩
    exact h z hz a ha

end BoxGen

section Slice

variable {K : Type*} [Ring K] [Algebra ℚ K]

def s1_coord {ι : Type*} (b : Module.Basis ι ℚ K) (i : ι) : K ⊗[ℚ] 𝔸f →ₗ[ℚ] 𝔸f :=
  TensorProduct.lift ((LinearMap.lsmul ℚ 𝔸f).comp (b.coord i))

theorem s1_coord_tmul {ι : Type*} (b : Module.Basis ι ℚ K) (i : ι) (z : K) (a : 𝔸f) :
    s1_coord b i (z ⊗ₜ[ℚ] a) = (b.repr z i) • a := by
  unfold s1_coord
  rw [TensorProduct.lift.tmul]
  rfl

theorem s1_coord_mem_Zhat_of_mem_finiteAdeleBox {ι : Type*} (b : Module.Basis ι ℚ K) (i : ι)
    {t : K ⊗[ℚ] 𝔸f} (ht : t ∈ Submodule.finiteAdeleBox (Submodule.span ℤ (Set.range b))) :
    s1_coord b i t ∈ s1_Zhat := by
  have hle : Submodule.finiteAdeleBox (Submodule.span ℤ (Set.range b))
      ≤ (s1_Zhat.toAddSubgroup).comap (s1_coord b i).toAddMonoidHom := by
    rw [s1_finiteAdeleBox_le_iff]
    intro z hz a ha
    rw [AddSubgroup.mem_comap]
    show s1_coord b i (z ⊗ₜ[ℚ] a) ∈ s1_Zhat
    rw [s1_coord_tmul]
    obtain ⟨m, hm⟩ := (Module.Basis.mem_span_iff_repr_mem ℤ b z).mp hz i
    rw [← hm, Algebra.smul_def]
    refine mul_mem ?_ ha
    have : (algebraMap ℤ ℚ m) = ((m : ℤ) : ℚ) := by rw [algebraMap_int_eq, Int.coe_castRingHom]
    rw [this]
    exact s1_algebraMap_intCast_mem_Zhat m
  exact hle ht

theorem s1_tmul_one_mem_finiteAdeleBox_iff {ι : Type*} [Fintype ι] (b : Module.Basis ι ℚ K) (z : K) :
    z ⊗ₜ[ℚ] (1 : 𝔸f) ∈ Submodule.finiteAdeleBox (Submodule.span ℤ (Set.range b))
      ↔ z ∈ Submodule.span ℤ (Set.range b) := by
  constructor
  · intro hz
    rw [Module.Basis.mem_span_iff_repr_mem ℤ b z]
    intro i
    have hc := s1_coord_mem_Zhat_of_mem_finiteAdeleBox b i hz
    rw [s1_coord_tmul, Algebra.smul_def, mul_one] at hc
    have hval : ∀ v : HOS, v.valuation ℚ (b.repr z i) ≤ 1 := fun v =>
      (s1_algebraMap_apply_mem_integers_iff _ v).mp (hc v)
    obtain ⟨m, hm⟩ := s1_exists_intCast_of_forall_valuation_le_one _ hval
    refine ⟨m, ?_⟩
    rw [hm, algebraMap_int_eq, Int.coe_castRingHom]
  · intro hz
    exact s1_tmul_mem_finiteAdeleBox hz (one_mem _)

end Slice

section LatticeBasis

variable {K : Type*} [Ring K] [Algebra ℚ K]

theorem s1_exists_basis_of_isLattice (M : Submodule ℤ K) [Submodule.IsLattice ℚ M] :
    ∃ (n : ℕ) (bM : Module.Basis (Fin n) ℚ K), Submodule.span ℤ (Set.range bM) = M := by
  classical
  haveI : Module.Finite ℤ ↥M := Submodule.IsLattice.finite ℚ _
  haveI : Module.Free ℤ ↥M := Submodule.IsLattice.free ℚ _
  let n := Module.finrank ℤ ↥M
  let bZ : Module.Basis (Fin n) ℤ ↥M := Module.finBasis ℤ ↥M
  refine ⟨n, bZ.extendOfIsLattice ℚ, ?_⟩
  have hrange : Set.range (bZ.extendOfIsLattice ℚ) = M.subtype '' Set.range bZ := by
    ext x
    simp only [Set.mem_range, Module.Basis.extendOfIsLattice_apply, Set.mem_image,
      Submodule.coe_subtype]
    exact ⟨fun ⟨k, hk⟩ => ⟨bZ k, ⟨k, rfl⟩, hk⟩, fun ⟨y, ⟨k, hk⟩, hy⟩ => ⟨k, by rw [hk]; exact hy⟩⟩
  rw [hrange, ← Submodule.map_span, bZ.span_eq, Submodule.map_top, Submodule.range_subtype]

end LatticeBasis

section FG
variable {K : Type*} [Ring K] [Algebra ℚ K]

theorem s3_fg_of_le {M N : Submodule ℤ K} [Submodule.IsLattice ℚ N] (hle : M ≤ N) : M.FG := by
  haveI : IsNoetherian ℤ ↥N := isNoetherian_of_fg_of_noetherian _ (Submodule.IsLattice.fg (A := ℚ))
  have hrw : M = Submodule.map N.subtype (Submodule.comap N.subtype M) := by
    rw [Submodule.map_comap_subtype]; exact (inf_of_le_right hle).symm
  rw [hrw]; exact (IsNoetherian.noetherian _).map _
end FG

section Multiplier
variable {K : Type*} [Ring K] [Algebra ℚ K]

theorem s3_exists_natCast_smul_mem (Λ : Submodule ℤ K) [Submodule.IsLattice ℚ Λ] (z : K) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : ℚ) • z ∈ Λ := by
  classical
  obtain ⟨m, b, hb⟩ := s1_exists_basis_of_isLattice Λ

  refine ⟨∏ i, (b.repr z i).den, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => (b.repr z i).den_nz
  · rw [← hb, Module.Basis.mem_span_iff_repr_mem ℤ b]
    intro i
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    have hdvd : ((b.repr z i).den : ℤ) ∣ ((∏ j, (b.repr z j).den : ℕ) : ℤ) := by
      exact_mod_cast Finset.dvd_prod_of_mem (fun j => (b.repr z j).den) (Finset.mem_univ i)
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k * (b.repr z i).num, ?_⟩
    show ((k * (b.repr z i).num : ℤ) : ℚ) = ((∏ j, (b.repr z j).den : ℕ) : ℚ) * b.repr z i
    have hq : ((b.repr z i).den : ℚ) * (b.repr z i) = (b.repr z i).num := by
      rw [mul_comm]; exact Rat.mul_den_eq_num (b.repr z i)
    have hk' : ((∏ j, (b.repr z j).den : ℕ) : ℚ) = ((b.repr z i).den : ℚ) * (k : ℚ) := by
      exact_mod_cast hk
    rw [hk', mul_comm ((b.repr z i).den : ℚ) (k : ℚ), mul_assoc, hq, Int.cast_mul]

end Multiplier

section ConjBox

variable {K : Type*} [Ring K] [Algebra ℚ K]

abbrev q15_cj (g : (K ⊗[ℚ] 𝔸f)ˣ) : (K ⊗[ℚ] 𝔸f) →+ (K ⊗[ℚ] 𝔸f) :=
  (AddMonoidHom.mulRight ((g⁻¹ : (K ⊗[ℚ] 𝔸f)ˣ) : K ⊗[ℚ] 𝔸f)).comp (AddMonoidHom.mulLeft (g : K ⊗[ℚ] 𝔸f))

theorem q15_cj_apply (g : (K ⊗[ℚ] 𝔸f)ˣ) (t : K ⊗[ℚ] 𝔸f) :
    (q15_cj g) t = (g : K ⊗[ℚ] 𝔸f) * t * ((g⁻¹ : (K ⊗[ℚ] 𝔸f)ˣ) : K ⊗[ℚ] 𝔸f) := by
  rw [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]

theorem q15_mem_conj_iff_exists (Λ : Submodule ℤ K) (g : (K ⊗[ℚ] 𝔸f)ˣ) (z : K) :
    z ∈ Submodule.conjByFiniteIdele Λ g ↔
      ∃ u ∈ Submodule.finiteAdeleBox Λ,
        (g : K ⊗[ℚ] 𝔸f) * u * ((g⁻¹ : (K ⊗[ℚ] 𝔸f)ˣ) : K ⊗[ℚ] 𝔸f) = z ⊗ₜ[ℚ] (1 : 𝔸f) := by
  show z ⊗ₜ[ℚ] (1 : 𝔸f) ∈ (Submodule.finiteAdeleBox Λ).map (q15_cj g) ↔ _
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨u, hu, h⟩; exact ⟨u, hu, by rw [← q15_cj_apply]; exact h⟩
  · rintro ⟨u, hu, h⟩; exact ⟨u, hu, by rw [q15_cj_apply]; exact h⟩

theorem q15_mem_conj_iff_conj_mem (Λ : Submodule ℤ K) (g : (K ⊗[ℚ] 𝔸f)ˣ) (z : K) :
    z ∈ Submodule.conjByFiniteIdele Λ g ↔
      ((g⁻¹ : (K ⊗[ℚ] 𝔸f)ˣ) : K ⊗[ℚ] 𝔸f) * (z ⊗ₜ[ℚ] (1 : 𝔸f)) * (g : K ⊗[ℚ] 𝔸f)
        ∈ Submodule.finiteAdeleBox Λ := by
  rw [q15_mem_conj_iff_exists]
  constructor
  · rintro ⟨u, hu, h⟩
    have : ((g⁻¹ : (K ⊗[ℚ] 𝔸f)ˣ) : K ⊗[ℚ] 𝔸f) * (z ⊗ₜ[ℚ] (1 : 𝔸f)) * (g : K ⊗[ℚ] 𝔸f) = u := by
      rw [← h, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [this]; exact hu
  · intro h
    refine ⟨_, h, ?_⟩
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]

end ConjBox

end AdelicSlice

end

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

noncomputable section

namespace STAB

open AdelicSlice

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

theorem isLattice_of_isOrder {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) :
    Submodule.IsLattice ℚ Λ := ⟨hΛ.fg, hΛ.spanTop⟩

theorem tmul_one_mem_box_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (z : ℍ[ℚ, a, b]) :
    z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ ↔ z ∈ Λ := by
  haveI := isLattice_of_isOrder hΛ
  obtain ⟨n, bΛ, hb⟩ := s1_exists_basis_of_isLattice Λ
  rw [← hb]
  exact s1_tmul_one_mem_finiteAdeleBox_iff bΛ z

theorem conj_one {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) :
    Submodule.conjByFiniteIdele Λ 1 = Λ := by
  ext z
  rw [q15_mem_conj_iff_conj_mem, inv_one, Units.val_one, one_mul, mul_one, tmul_one_mem_box_iff hΛ]

theorem conj_mul {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (g g' : (ℍ𝔸)ˣ) :
    Submodule.conjByFiniteIdele Λ (g * g') = Submodule.conjByFiniteIdele (Submodule.conjByFiniteIdele Λ g') g := by
  ext z
  rw [q15_mem_conj_iff_conj_mem, q15_mem_conj_iff_exists,
    Submodule.finiteAdeleBox_conjByFiniteIdele Λ hΛ.fg hΛ.spanTop g']
  set t : ℍ𝔸 := z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) with ht
  constructor
  · intro h
    refine ⟨((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * t * (g : ℍ𝔸), ?_, ?_⟩
    · refine ⟨(((g * g')⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * t * ((g * g' : (ℍ𝔸)ˣ) : ℍ𝔸), h, ?_⟩
      rw [mul_inv_rev, Units.val_mul, Units.val_mul]
      show (g' : ℍ𝔸) * (((g'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * t * ((g : ℍ𝔸) * (g' : ℍ𝔸))) *
          ((g'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * t * (g : ℍ𝔸)
      rw [show (g' : ℍ𝔸) * (((g'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * t * ((g : ℍ𝔸) * (g' : ℍ𝔸))) *
          ((g'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = ((g' : ℍ𝔸) * ((g'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * (((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * t * (g : ℍ𝔸)) *
          ((g' : ℍ𝔸) * ((g'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) by noncomm_ring]
      rw [Units.mul_inv, one_mul, mul_one]
    · rw [show (g : ℍ𝔸) * (((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * t * (g : ℍ𝔸)) * ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) =
          ((g : ℍ𝔸) * ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * t * ((g : ℍ𝔸) * ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) by noncomm_ring]
      rw [Units.mul_inv, one_mul, mul_one]
  · rintro ⟨u, ⟨w, hw, rfl⟩, hu⟩
    rw [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight] at hu

    have : (((g * g')⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * t * ((g * g' : (ℍ𝔸)ˣ) : ℍ𝔸) = w := by
      rw [← hu, mul_inv_rev, Units.val_mul, Units.val_mul]
      rw [show ((g'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((g : ℍ𝔸) * ((g' : ℍ𝔸) * w * ((g'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) *
          ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * ((g : ℍ𝔸) * (g' : ℍ𝔸)) =
          ((g'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (g : ℍ𝔸)) * (g' : ℍ𝔸) * w *
            (((g'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (g : ℍ𝔸)) * (g' : ℍ𝔸)) by noncomm_ring]
      rw [Units.inv_mul, mul_one, Units.inv_mul, one_mul, mul_one]
    rw [this]; exact hw

theorem conj_unit {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : QuaternionAlgebra.IsOrder X) {u : (ℍ𝔸)ˣ}
    (hu : u ∈ Submodule.finiteIdeleStabilizer X) : Submodule.conjByFiniteIdele X u = X := by
  rw [← one_mul u, Submodule.conjByFiniteIdele_mul_eq_of_mem_finiteIdeleStabilizer X hX.one_mem
    (fun x y hx hy => hX.mul_mem hx hy) 1 u hu, conj_one hX]

theorem conj_mono {X Y : Submodule ℤ ℍ[ℚ, a, b]} (h : X ≤ Y) (g : (ℍ𝔸)ˣ) :
    Submodule.conjByFiniteIdele X g ≤ Submodule.conjByFiniteIdele Y g := by
  intro z hz
  rw [q15_mem_conj_iff_conj_mem] at hz ⊢
  exact HeckeLocal.box_mono h hz

theorem isOrder_meetOrder {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) (n : (ℍ𝔸)ˣ) :
    QuaternionAlgebra.IsOrder (CerednikDrinfeld.meetOrder R n) := by
  have hRn := QuaternionAlgebra.IsOrder.conjByFiniteIdele R hR n
  haveI := isLattice_of_isOrder hR
  haveI := isLattice_of_isOrder hRn
  refine ⟨⟨hR.one_mem, hRn.one_mem⟩, fun x y hx hy => ⟨hR.mul_mem hx.1 hy.1, hRn.mul_mem hx.2 hy.2⟩, ?_, ?_⟩
  ·
    rw [eq_top_iff]
    intro z _
    obtain ⟨m, hm, hmz⟩ := s3_exists_natCast_smul_mem R z
    obtain ⟨m', hm', hm'z⟩ := s3_exists_natCast_smul_mem (Submodule.conjByFiniteIdele R n) z
    have hmem : ((m * m' : ℕ) : ℚ) • z ∈ CerednikDrinfeld.meetOrder R n := by
      refine ⟨?_, ?_⟩
      · rw [Nat.cast_mul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul ℚ m']
        exact Submodule.smul_of_tower_mem _ m' hmz
      · rw [Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul ℚ m]
        exact Submodule.smul_of_tower_mem _ m hm'z
    have hne : ((m * m' : ℕ) : ℚ) ≠ 0 := by exact_mod_cast mul_ne_zero hm hm'
    have : z = ((m * m' : ℕ) : ℚ)⁻¹ • (((m * m' : ℕ) : ℚ) • z) := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  · exact s3_fg_of_le (N := R) inf_le_left

theorem stabU (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : QuaternionAlgebra.IsOrder R) (n : (ℍ𝔸)ˣ) (q : ℕ) {u h : (ℍ𝔸)ˣ}
    (hu : u ∈ Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n))
    (hh : h ∈ CerednikDrinfeld.uHeckeSet R n q) :
    u * h ∈ CerednikDrinfeld.uHeckeSet R n q ∧ h * u ∈ CerednikDrinfeld.uHeckeSet R n q := by
  have hRn := QuaternionAlgebra.IsOrder.conjByFiniteIdele R hR n
  have hS := isOrder_meetOrder hR n
  have huR : u ∈ Submodule.finiteIdeleStabilizer R := HeckeLocal.stabilizer_mono hS hR inf_le_left hu
  have huRn : u ∈ Submodule.finiteIdeleStabilizer (Submodule.conjByFiniteIdele R n) :=
    HeckeLocal.stabilizer_mono hS hRn inf_le_right hu
  obtain ⟨hp, hA, hB⟩ := hh
  refine ⟨⟨HeckeLocal.mul_mem_primeHeckeSet_of_mem_stabilizer hS q hu hp, ?_, ?_⟩,
    ⟨HeckeLocal.mul_mem_primeHeckeSet_of_mem_stabilizer' hS q hu hp, ?_, ?_⟩⟩
  · rw [conj_mul hRn u h, hA, conj_unit hR huR]
  · intro heq
    apply hB
    calc Submodule.conjByFiniteIdele R h
        = Submodule.conjByFiniteIdele R (u⁻¹ * (u * h)) := by rw [inv_mul_cancel_left]
      _ = Submodule.conjByFiniteIdele (Submodule.conjByFiniteIdele R (u * h)) u⁻¹ := conj_mul hR u⁻¹ (u * h)
      _ = Submodule.conjByFiniteIdele R n := by rw [heq, conj_unit hRn (inv_mem huRn)]
  · rw [Submodule.conjByFiniteIdele_mul_eq_of_mem_finiteIdeleStabilizer _ hRn.one_mem (fun x y hx hy => hRn.mul_mem hx hy)
      h u huRn, hA]
  · rw [Submodule.conjByFiniteIdele_mul_eq_of_mem_finiteIdeleStabilizer _ hR.one_mem (fun x y hx hy => hR.mul_mem hx hy)
      h u huR]
    exact hB

theorem stabL (Λ O : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ) (hO : QuaternionAlgebra.IsOrder O)
    (hOΛ : O ≤ Λ) (ℓ : ℕ) {u h : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer O)
    (hh : h ∈ CerednikDrinfeld.levelHeckeUSet Λ O ℓ) :
    u * h ∈ CerednikDrinfeld.levelHeckeUSet Λ O ℓ ∧ h * u ∈ CerednikDrinfeld.levelHeckeUSet Λ O ℓ := by
  have huΛ : u ∈ Submodule.finiteIdeleStabilizer Λ := HeckeLocal.stabilizer_mono hO hΛ hOΛ hu
  obtain ⟨hp, hA, hB⟩ := hh
  refine ⟨⟨HeckeLocal.mul_mem_primeHeckeSet_of_mem_stabilizer hO ℓ hu hp, ?_, ?_⟩,
    ⟨HeckeLocal.mul_mem_primeHeckeSet_of_mem_stabilizer' hO ℓ hu hp, ?_, ?_⟩⟩
  · intro heq
    apply hA
    calc Submodule.conjByFiniteIdele O h
        = Submodule.conjByFiniteIdele O (u⁻¹ * (u * h)) := by rw [inv_mul_cancel_left]
      _ = Submodule.conjByFiniteIdele (Submodule.conjByFiniteIdele O (u * h)) u⁻¹ := conj_mul hO u⁻¹ (u * h)
      _ = O := by rw [heq, conj_unit hO (inv_mem hu)]
  · intro hle
    apply hB
    have h1 := conj_mono hle u⁻¹
    rw [conj_unit hO (inv_mem hu), ← conj_mul hΛ u⁻¹ (u * h), inv_mul_cancel_left] at h1
    exact h1
  · rw [Submodule.conjByFiniteIdele_mul_eq_of_mem_finiteIdeleStabilizer _ hO.one_mem (fun x y hx hy => hO.mul_mem hx hy)
      h u hu]
    exact hA
  · rw [Submodule.conjByFiniteIdele_mul_eq_of_mem_finiteIdeleStabilizer _ hΛ.one_mem (fun x y hx hy => hΛ.mul_mem hx hy)
      h u huΛ]
    exact hB

end STAB

end

open scoped TensorProduct Quaternion in
open IsDedekindDomain NumberField in

theorem solution
    {a b : ℚ} (Λ O : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ) (hO : QuaternionAlgebra.IsOrder O)
    (hOΛ : O ≤ Λ) (ℓ : ℕ)
    {u h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hu : u ∈ Submodule.finiteIdeleStabilizer O)
    (hh : h ∈ CerednikDrinfeld.levelHeckeUSet Λ O ℓ) :
    u * h ∈ CerednikDrinfeld.levelHeckeUSet Λ O ℓ ∧ h * u ∈ CerednikDrinfeld.levelHeckeUSet Λ O ℓ :=
  STAB.stabL Λ O hΛ hO hOΛ ℓ hu hh

end S_CerednikDrinfeld_mul_mem_levelHeckeUSet_and_mul_mem_levelHeckeUSet_of_mem_finiteIdeleStabilizer
end P2MW
export P2MW.S_CerednikDrinfeld_mul_mem_levelHeckeUSet_and_mul_mem_levelHeckeUSet_of_mem_finiteIdeleStabilizer (solution)
