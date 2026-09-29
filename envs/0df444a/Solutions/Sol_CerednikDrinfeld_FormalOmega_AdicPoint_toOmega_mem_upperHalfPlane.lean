-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.AdicPoint.toOmega_mem_upperHalfPlane
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0ef86ea1-267f-5f56-bccb-3fc1f72df7b5

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
p2m_open "LT.LatticeTree CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane.CerednikDrinfeld CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane.CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.upperHalfPlane"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt modPow span_pow_succ_le modPowTransition AdicPoint stdFullLattice stdBasisVec coordToTensor AdicPoint.mem_stdLine_iff AdicPoint.lineC AdicPoint.vecCons_toOmega_mem coe_ofEq_apply actBaseChange_tmul rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum lineBaseChange"
namespace LevelAux
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

open TensorProduct

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']

theorem mem_smul_top_of_rTensor_eq_zero (f : B →ₐ[𝒪] B') (hf : Function.Surjective f) (M : FullLattice 𝒪 K)
    (𝔭' : Ideal B') (y : latticeBaseChange 𝒪 K B M) (hy : LinearMap.rTensor (↥M.1) f.toLinearMap y = 0) :
    y ∈ (Ideal.comap f 𝔭' • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)) := by
  have hex := rTensor_exact (↥M.1) (LinearMap.exact_subtype_ker_map f.toLinearMap) hf
  obtain ⟨z, rfl⟩ := (hex y).mp hy
  clear hy
  induction z using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero]; exact zero_mem _
  | add a b ha hb => rw [LinearMap.map_add]; exact add_mem ha hb
  | tmul k v =>
    rw [LinearMap.rTensor_tmul, Submodule.subtype_apply]
    have hk : (k : B) ∈ Ideal.comap f 𝔭' := by
      rw [Ideal.mem_comap]
      have : f (k : B) = 0 := k.2
      rw [this]; exact zero_mem _
    have : (k : B) ⊗ₜ[𝒪] v = (k : B) • ((1 : B) ⊗ₜ[𝒪] v) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem_smul hk Submodule.mem_top

theorem exists_preimage_of_mem_smul_top (f : B →ₐ[𝒪] B') (hf : Function.Surjective f) (M : FullLattice 𝒪 K)
    (𝔭' : Ideal B') (z : latticeBaseChange 𝒪 K B' M) (hz : z ∈ (𝔭' • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' M))) :
    ∃ u ∈ (Ideal.comap f 𝔭' • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)),
      LinearMap.rTensor (↥M.1) f.toLinearMap u = z := by
  refine Submodule.smul_induction_on
    (p := fun z => ∃ u ∈ (Ideal.comap f 𝔭' • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)),
      LinearMap.rTensor (↥M.1) f.toLinearMap u = z) hz (fun p' hp' w _ => ?_) (fun a b ha hb => ?_)
  · obtain ⟨p, rfl⟩ := hf p'
    obtain ⟨w₀, rfl⟩ := LinearMap.rTensor_surjective (↥M.1) (show Function.Surjective f.toLinearMap from hf) w
    refine ⟨p • w₀, Submodule.smul_mem_smul (Ideal.mem_comap.mpr hp') Submodule.mem_top, ?_⟩
    rw [rTensor_smul_left]
  · obtain ⟨u, hu, rfl⟩ := ha
    obtain ⟨u', hu', rfl⟩ := hb
    exact ⟨u + u', add_mem hu hu', by rw [LinearMap.map_add]⟩

theorem exists_preimage_of_mem_lineBaseChange (f : B →ₐ[𝒪] B') (hf : Function.Surjective f) (M : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B M)) (z : latticeBaseChange 𝒪 K B' M) (hz : z ∈ lineBaseChange f M N) :
    ∃ y ∈ N, LinearMap.rTensor (↥M.1) f.toLinearMap y = z := by
  rw [lineBaseChange] at hz
  induction hz using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨y, hy, rfl⟩ := hs
    exact ⟨y, hy, rfl⟩
  | zero => exact ⟨0, zero_mem _, by rw [LinearMap.map_zero]⟩
  | add a b _ _ ha hb =>
    obtain ⟨u, hu, rfl⟩ := ha
    obtain ⟨u', hu', rfl⟩ := hb
    exact ⟨u + u', add_mem hu hu', by rw [LinearMap.map_add]⟩
  | smul b' a _ ha =>
    obtain ⟨u, hu, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hf b'
    exact ⟨b • u, Submodule.smul_mem _ _ hu, by rw [rTensor_smul_left]⟩

theorem one_tmul_mem_sup_iff (f : B →ₐ[𝒪] B') (hf : Function.Surjective f) (M : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B M)) (𝔭' : Ideal B') (v : ↥M.1) :
    (1 : B') ⊗ₜ[𝒪] v ∈ lineBaseChange f M N ⊔ (𝔭' • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' M)) ↔
      (1 : B) ⊗ₜ[𝒪] v ∈ N ⊔ (Ideal.comap f 𝔭' • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)) := by
  set T := LinearMap.rTensor (↥M.1) f.toLinearMap with hT
  have hTv : T ((1 : B) ⊗ₜ[𝒪] v) = (1 : B') ⊗ₜ[𝒪] v := by rw [hT]; exact rTensor_one_tmul f M v
  constructor
  · intro h
    obtain ⟨z₁, hz₁, z₂, hz₂, hsum⟩ := Submodule.mem_sup.mp h
    obtain ⟨y₁, hy₁, rfl⟩ := exists_preimage_of_mem_lineBaseChange f hf M N z₁ hz₁
    obtain ⟨y₂, hy₂, rfl⟩ := exists_preimage_of_mem_smul_top f hf M 𝔭' z₂ hz₂
    have hker : T ((1 : B) ⊗ₜ[𝒪] v - y₁ - y₂) = 0 := by
      rw [map_sub, map_sub, hTv, ← hsum, hT]; abel
    have hmem := mem_smul_top_of_rTensor_eq_zero f hf M 𝔭' _ hker
    have : (1 : B) ⊗ₜ[𝒪] v = y₁ + (((1 : B) ⊗ₜ[𝒪] v - y₁ - y₂) + y₂) := by abel
    rw [this]
    exact Submodule.mem_sup.mpr ⟨y₁, hy₁, _, add_mem hmem hy₂, rfl⟩
  · intro h
    obtain ⟨y₁, hy₁, y₂, hy₂, hsum⟩ := Submodule.mem_sup.mp h
    rw [← hTv, ← hsum, map_add]
    refine Submodule.mem_sup.mpr ⟨T y₁, ?_, T y₂, ?_, rfl⟩
    · rw [lineBaseChange, hT]
      exact Submodule.subset_span ⟨y₁, hy₁, rfl⟩
    · refine Submodule.smul_induction_on (p := fun y => T y ∈ (𝔭' • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' M)))
        hy₂ (fun p hp w _ => ?_) (fun a b ha hb => ?_)
      · show T (p • w) ∈ _
        rw [hT, rTensor_smul_left]
        exact Submodule.smul_mem_smul (Ideal.mem_comap.mp hp) Submodule.mem_top
      · show T (a + b) ∈ _
        rw [map_add]; exact add_mem ha hb

theorem vertexNondegAt_map_iff (f : B →ₐ[𝒪] B') (hf : Function.Surjective f) (d : DeligneDatum (K := K) π B)
    (𝔭' : Ideal B') (M : FullLattice 𝒪 K) :
    (d.map π f).VertexNondegAt π 𝔭' M ↔ d.VertexNondegAt π (Ideal.comap f 𝔭') M := by
  unfold DeligneDatum.VertexNondegAt
  refine forall_congr' fun v => imp_congr_right fun _ => not_congr ?_
  exact one_tmul_mem_sup_iff f hf M (d.line M) 𝔭' v

theorem edgeNondegAt_map_iff (f : B →ₐ[𝒪] B') (hf : Function.Surjective f) (d : DeligneDatum (K := K) π B)
    (𝔭' : Ideal B') (M' M : FullLattice 𝒪 K) :
    (d.map π f).EdgeNondegAt π 𝔭' M' M ↔ d.EdgeNondegAt π (Ideal.comap f 𝔭') M' M := by
  unfold DeligneDatum.EdgeNondegAt
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr ?_ ?_
  · refine forall_congr' fun v => imp_congr_right fun _ => not_congr ?_
    exact one_tmul_mem_sup_iff f hf M (d.line M) 𝔭' v
  · refine forall_congr' fun v' => imp_congr_right fun _ => not_congr ?_
    exact one_tmul_mem_sup_iff f hf M' (d.line M') 𝔭' v'

variable {R : Type} [CommRing R] [Algebra 𝒪 R]

theorem span_pow_le_span_one (π : 𝒪) (n : ℕ) :
    Ideal.span {algebraMap 𝒪 R π ^ (n + 1)} ≤ Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)} :=
  Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.succ_le_succ (Nat.zero_le n)))

def red (π : 𝒪) (n : ℕ) : modPow π R n →ₐ[𝒪] modPow π R 0 :=
  Ideal.Quotient.factorₐ 𝒪 (span_pow_le_span_one π n)

theorem red_surjective (π : 𝒪) (n : ℕ) : Function.Surjective (red (R := R) π n) :=
  Ideal.Quotient.factor_surjective (span_pow_le_span_one π n)

theorem red_zero_eq_id (π : 𝒪) : red (R := R) π 0 = AlgHom.id 𝒪 (modPow π R 0) := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro r
  rfl

theorem red_succ (π : 𝒪) (n : ℕ) : red (R := R) π (n + 1) = (red π n).comp (modPowTransition π R n) := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro r
  rfl

theorem map_red_pt (x : AdicPoint K π R) (n : ℕ) : DeligneDatum.map π (red π n) (x.pt n) = x.pt 0 := by
  induction n with
  | zero =>
    rw [red_zero_eq_id]
    exact (Omega K π).map_id (x.pt 0)
  | succ n ih =>
    rw [red_succ]
    have hc := (Omega K π).map_comp (modPowTransition π R n) (red π n) (x.pt (n + 1))
    change DeligneDatum.map π ((red π n).comp (modPowTransition π R n)) (x.pt (n + 1)) =
      DeligneDatum.map π (red π n) (DeligneDatum.map π (modPowTransition π R n) (x.pt (n + 1))) at hc
    rw [hc, x.compat n, ih]

theorem ker_red_le (π : 𝒪) (n : ℕ) (𝔮 : Ideal (modPow π R n)) [𝔮.IsPrime] :
    RingHom.ker (red (R := R) π n) ≤ 𝔮 := by
  intro b hb
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [RingHom.mem_ker] at hb
  change Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)}) r = 0 at hb
  rw [Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one, Ideal.mem_span_singleton] at hb
  obtain ⟨s, rfl⟩ := hb
  apply Ideal.IsPrime.mem_of_pow_mem ‹_› (n + 1)
  have h0 : (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) (algebraMap 𝒪 R π * s)) ^ (n + 1) = 0 := by
    rw [← map_pow (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})) (algebraMap 𝒪 R π * s) (n + 1),
      Ideal.Quotient.eq_zero_iff_mem, mul_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  rw [h0]
  exact zero_mem _

theorem comap_map_red (π : 𝒪) (n : ℕ) (𝔮 : Ideal (modPow π R n)) [𝔮.IsPrime] :
    Ideal.comap (red (R := R) π n) (Ideal.map (red (R := R) π n) 𝔮) = 𝔮 := by
  rw [Ideal.comap_map_of_surjective _ (red_surjective π n), sup_eq_left]
  intro b hb
  exact ker_red_le π n 𝔮 ((RingHom.mem_ker).mpr (by simpa [Ideal.mem_comap] using hb))

end CerednikDrinfeld.FormalOmega.LevelAux

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.upperHalfPlane"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt modPow span_pow_succ_le modPowTransition AdicPoint stdFullLattice stdBasisVec coordToTensor AdicPoint.mem_stdLine_iff AdicPoint.lineC AdicPoint.vecCons_toOmega_mem coe_ofEq_apply actBaseChange_tmul rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum lineBaseChange"
namespace T2aAux
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

open TensorProduct

section Frame

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
  {C : Type} [Field C] [Algebra K C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]
  {ϖ : PseudoUniformizer K C}

theorem isUnit_iff_v_eq_one (hF : IsAdicFrame π ϖ R) (r : R) : IsUnit r ↔ Valued.v (algebraMap R C r) = 1 := by
  constructor
  · intro hr
    obtain ⟨u, rfl⟩ := hr
    apply le_antisymm (hF.v_algebraMap_le_one _)
    have h1 : Valued.v (algebraMap R C (u : R)) * Valued.v (algebraMap R C (↑u⁻¹ : R)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have h2 := hF.v_algebraMap_le_one (↑u⁻¹ : R)
    by_contra hlt
    have hlt' : Valued.v (algebraMap R C (u : R)) < 1 := not_le.mp hlt
    have : Valued.v (algebraMap R C (u : R)) * Valued.v (algebraMap R C (↑u⁻¹ : R)) < 1 :=
      mul_lt_one_of_lt_of_le hlt' h2
    rw [h1] at this
    exact lt_irrefl _ this
  · intro hv
    have hne : algebraMap R C r ≠ 0 := fun h => by rw [h, map_zero] at hv; exact zero_ne_one hv
    obtain ⟨s, hs⟩ := (hF.range_eq (algebraMap R C r)⁻¹).mp (by rw [map_inv₀, hv, inv_one])
    refine ⟨⟨r, s, hF.injective ?_, hF.injective ?_⟩, rfl⟩
    · rw [map_mul, hs, mul_inv_cancel₀ hne, map_one]
    · rw [map_mul, hs, inv_mul_cancel₀ hne, map_one]

theorem mem_nonunits_iff' (hF : IsAdicFrame π ϖ R) (r : R) : r ∈ nonunits R ↔ Valued.v (algebraMap R C r) < 1 := by
  rw [mem_nonunits_iff, isUnit_iff_v_eq_one hF]
  exact ⟨fun h => lt_of_le_of_ne (hF.v_algebraMap_le_one r) h, fun h => h.ne⟩

theorem nontrivial (hF : IsAdicFrame π ϖ R) : Nontrivial R :=
  ⟨⟨0, 1, fun h => by
    have := congrArg (algebraMap R C) h
    rw [map_zero, map_one] at this
    exact zero_ne_one this⟩⟩

theorem isLocalRing (hF : IsAdicFrame π ϖ R) : IsLocalRing R := by
  haveI := nontrivial hF
  refine IsLocalRing.of_nonunits_add fun a b ha hb => ?_
  rw [mem_nonunits_iff' hF] at ha hb ⊢
  rw [map_add]
  exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)

theorem pi_mem_nonunits (hF : IsAdicFrame π ϖ R) : algebraMap 𝒪 R π ∈ nonunits R := by
  rw [mem_nonunits_iff' hF, ← IsScalarTower.algebraMap_apply]
  exact hF.v_algebraMap_lt_one

theorem isLocalRing_modPow (hF : IsAdicFrame π ϖ R) (n : ℕ) : IsLocalRing (modPow π R n) := by
  haveI := isLocalRing hF
  haveI : Nontrivial (modPow π R n) := by
    refine Ideal.Quotient.nontrivial_iff.mpr ?_
    rw [Ne, Ideal.eq_top_iff_one, Ideal.mem_span_singleton]
    intro h
    exact pi_mem_nonunits hF (isUnit_of_dvd_one (dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero n)) h))
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

end Frame

section StdBasis

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] (K : Type) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]

theorem linearIndependent_single : LinearIndependent 𝒪 (fun j : Fin 2 => (Pi.single j 1 : Fin 2 → K)) := by
  haveI : FaithfulSMul 𝒪 K := (faithfulSMul_iff_algebraMap_injective 𝒪 K).mpr (IsFractionRing.injective 𝒪 K)
  exact LinearIndependent.restrict_scalars' 𝒪 (Pi.linearIndependent_single_one (Fin 2) K)

noncomputable def stdBasis : Module.Basis (Fin 2) 𝒪 ↥(stdFullLattice (𝒪 := 𝒪) K).1 :=
  (Module.Basis.span (linearIndependent_single K)).map
    (LinearEquiv.ofEq _ _ (stdLattice_eq_span 𝒪 K).symm)

theorem stdBasis_apply (i : Fin 2) : stdBasis K i = stdBasisVec (𝒪 := 𝒪) K i := by
  apply Subtype.ext
  rw [stdBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.span_apply]
  rfl

variable (B : Type) [CommRing B] [Algebra 𝒪 B]

noncomputable def coordEquiv : latticeBaseChange 𝒪 K B (stdFullLattice K) ≃ₗ[B] (Fin 2 → B) :=
  ((stdBasis K).baseChange B).equivFun

theorem coordEquiv_tmul (b : B) (i : Fin 2) :
    coordEquiv K B (b ⊗ₜ[𝒪] stdBasisVec K i) = Pi.single i b := by
  rw [← stdBasis_apply]
  ext j
  rw [coordEquiv, Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul, Module.Basis.repr_self]
  by_cases hij : j = i
  · subst hij
    rw [Finsupp.single_eq_same, Pi.single_eq_same, one_smul]
  · have hij' : i ≠ j := fun h => hij h.symm
    simp [Finsupp.single_apply, Pi.single_apply, hij, hij']

theorem coordEquiv_symm_apply (w : Fin 2 → B) :
    (coordEquiv K B).symm w = ∑ i : Fin 2, w i ⊗ₜ[𝒪] stdBasisVec K i := by
  rw [coordEquiv, Module.Basis.equivFun_symm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.Basis.baseChange_apply, stdBasis_apply, smul_tmul', smul_eq_mul, mul_one]

end StdBasis

section Coord

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] (K : Type) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (π : 𝒪)
  (R : Type) [CommRing R] [Algebra 𝒪 R]

theorem coordEquiv_coordToTensor (n : ℕ) (w : Fin 2 → R) :
    coordEquiv (𝒪 := 𝒪) K (modPow π R n) (coordToTensor K π R n w) =
      fun i => Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) (w i) := by
  apply (coordEquiv (𝒪 := 𝒪) K (modPow π R n)).symm.injective
  rw [LinearEquiv.symm_apply_apply, coordEquiv_symm_apply]
  rfl

end Coord

section LocalLine

variable {B : Type} [CommRing B]

def vec (a b : B) : Fin 2 → B := a • Pi.single 0 1 + b • Pi.single 1 1

@[scoped simp] theorem vec_apply_zero (a b : B) : vec a b 0 = a := by simp [vec]
@[scoped simp] theorem vec_apply_one (a b : B) : vec a b 1 = b := by simp [vec]

theorem eq_vec (w : Fin 2 → B) : w = vec (w 0) (w 1) := by
  funext j
  fin_cases j
  · exact (vec_apply_zero _ _).symm
  · exact (vec_apply_one _ _).symm

theorem vec_eq_vec_iff (a b a' b' : B) : vec a b = vec a' b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem smul_vec (r a b : B) : r • vec a b = vec (r * a) (r * b) := by
  rw [eq_vec (r • vec a b)]
  simp

theorem linearMap_vec (φ : (Fin 2 → B) →ₗ[B] B) (a b : B) :
    φ (vec a b) = a * φ (Pi.single 0 1) + b * φ (Pi.single 1 1) := by
  rw [vec, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

theorem ker_eq_span_of_isUnit_snd (φ : (Fin 2 → B) →ₗ[B] B) (u : Bˣ) (hu : (u : B) = φ (Pi.single 1 1)) :
    LinearMap.ker φ = Submodule.span B {vec 1 (-(↑u⁻¹ * φ (Pi.single 0 1)))} := by
  apply le_antisymm
  · intro w hw
    rw [LinearMap.mem_ker, eq_vec w, linearMap_vec, ← hu] at hw
    rw [Submodule.mem_span_singleton]
    refine ⟨w 0, ?_⟩
    rw [smul_vec]
    conv_rhs => rw [eq_vec w]
    rw [vec_eq_vec_iff, mul_one]
    refine ⟨rfl, ?_⟩
    have h2 : w 1 * ↑u = -(w 0 * φ (Pi.single 0 1)) := by linear_combination hw
    calc w 0 * -(↑u⁻¹ * φ (Pi.single 0 1)) = -(w 0 * φ (Pi.single 0 1)) * ↑u⁻¹ := by ring
      _ = w 1 * ↑u * ↑u⁻¹ := by rw [h2]
      _ = w 1 := by rw [mul_assoc, Units.mul_inv, mul_one]
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker, linearMap_vec, ← hu]
    calc 1 * φ (Pi.single 0 1) + -(↑u⁻¹ * φ (Pi.single 0 1)) * ↑u
        = φ (Pi.single 0 1) - φ (Pi.single 0 1) * (↑u⁻¹ * ↑u) := by ring
      _ = 0 := by rw [Units.inv_mul, mul_one, sub_self]

theorem ker_eq_span_of_isUnit_fst (φ : (Fin 2 → B) →ₗ[B] B) (u : Bˣ) (hu : (u : B) = φ (Pi.single 0 1)) :
    LinearMap.ker φ = Submodule.span B {vec (-(↑u⁻¹ * φ (Pi.single 1 1))) 1} := by
  apply le_antisymm
  · intro w hw
    rw [LinearMap.mem_ker, eq_vec w, linearMap_vec, ← hu] at hw
    rw [Submodule.mem_span_singleton]
    refine ⟨w 1, ?_⟩
    rw [smul_vec]
    conv_rhs => rw [eq_vec w]
    rw [vec_eq_vec_iff, mul_one]
    refine ⟨?_, rfl⟩
    have h2 : w 0 * ↑u = -(w 1 * φ (Pi.single 1 1)) := by linear_combination hw
    calc w 1 * -(↑u⁻¹ * φ (Pi.single 1 1)) = -(w 1 * φ (Pi.single 1 1)) * ↑u⁻¹ := by ring
      _ = w 0 * ↑u * ↑u⁻¹ := by rw [h2]
      _ = w 0 := by rw [mul_assoc, Units.mul_inv, mul_one]
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker, linearMap_vec, ← hu]
    calc -(↑u⁻¹ * φ (Pi.single 1 1)) * ↑u + 1 * φ (Pi.single 1 1)
        = φ (Pi.single 1 1) - φ (Pi.single 1 1) * (↑u⁻¹ * ↑u) := by ring
      _ = 0 := by rw [Units.inv_mul, mul_one, sub_self]

variable [IsLocalRing B]

theorem exists_eq_span_of_invertible (N : Submodule B (Fin 2 → B)) [Module.Invertible B ((Fin 2 → B) ⧸ N)] :
    (∃ c : B, N = Submodule.span B {vec 1 c}) ∨ (∃ c : B, N = Submodule.span B {vec c 1}) := by
  obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv.mp (inferInstance : Module.Free B ((Fin 2 → B) ⧸ N))
  let φ : (Fin 2 → B) →ₗ[B] B := e.toLinearMap ∘ₗ N.mkQ
  have hker : LinearMap.ker φ = N := by
    simp only [φ]
    rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot, Submodule.ker_mkQ]
  have hsurj : Function.Surjective φ := e.surjective.comp (Submodule.mkQ_surjective N)
  obtain ⟨w, hw⟩ := hsurj 1
  rw [eq_vec w, linearMap_vec] at hw
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hw with h0 | h1
  · right
    have hα : IsUnit (φ (Pi.single 0 1)) := isUnit_of_mul_isUnit_right h0
    exact ⟨_, hker ▸ ker_eq_span_of_isUnit_fst φ hα.unit hα.unit_spec⟩
  · left
    have hβ : IsUnit (φ (Pi.single 1 1)) := isUnit_of_mul_isUnit_right h1
    exact ⟨_, hker ▸ ker_eq_span_of_isUnit_snd φ hβ.unit hβ.unit_spec⟩

end LocalLine

section SpanVec

variable {B : Type} [CommRing B] {B' : Type} [CommRing B']

theorem mem_span_vec_one_iff (c : B) (w : Fin 2 → B) : w ∈ Submodule.span B {vec 1 c} ↔ w 1 = c * w 0 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩; simp [smul_vec, mul_comm]
  · intro h; refine ⟨w 0, ?_⟩; rw [smul_vec, mul_one]; conv_rhs => rw [eq_vec w]; rw [h, mul_comm]

theorem mem_span_vec_one_iff' (c : B) (w : Fin 2 → B) : w ∈ Submodule.span B {vec c 1} ↔ w 0 = c * w 1 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩; simp [smul_vec, mul_comm]
  · intro h; refine ⟨w 1, ?_⟩; rw [smul_vec, mul_one]; conv_rhs => rw [eq_vec w]; rw [h, mul_comm]

theorem eq_of_span_vec_one_eq {c c' : B} (h : Submodule.span B {vec 1 c} = Submodule.span B {vec 1 c'}) : c = c' := by
  have : vec (1 : B) c ∈ Submodule.span B {vec 1 c'} := h ▸ Submodule.mem_span_singleton_self _
  rw [mem_span_vec_one_iff] at this
  simpa using this

theorem eq_of_span_vec_one_eq' {c c' : B} (h : Submodule.span B {vec c 1} = Submodule.span B {vec c' 1}) : c = c' := by
  have : vec c (1 : B) ∈ Submodule.span B {vec c' 1} := h ▸ Submodule.mem_span_singleton_self _
  rw [mem_span_vec_one_iff'] at this
  simpa using this

theorem mul_eq_one_of_span_eq {c c' : B} (h : Submodule.span B {vec 1 c} = Submodule.span B {vec c' 1}) : c' * c = 1 := by
  have : vec (1 : B) c ∈ Submodule.span B {vec c' 1} := h ▸ Submodule.mem_span_singleton_self _
  rw [mem_span_vec_one_iff'] at this
  simpa [eq_comm] using this

theorem span_vec_unit (u : Bˣ) : Submodule.span B {vec (u : B) 1} = Submodule.span B {vec 1 (↑u⁻¹ : B)} := by
  apply le_antisymm
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_span_vec_one_iff]
    simp
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_span_vec_one_iff']
    simp

theorem span_vec_unit' (u : Bˣ) : Submodule.span B {vec 1 (u : B)} = Submodule.span B {vec (↑u⁻¹ : B) 1} := by
  rw [span_vec_unit u⁻¹, inv_inv]

theorem image_span_vec {F : Type} [FunLike F B B'] [RingHomClass F B B'] (f : F) (hf : Function.Surjective f) (a b : B) :
    (fun w : Fin 2 → B => fun i => f (w i)) '' (Submodule.span B {vec a b} : Set (Fin 2 → B)) =
      (Submodule.span B' {vec (f a) (f b)} : Set (Fin 2 → B')) := by
  ext w'
  simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨w, ⟨r, rfl⟩, rfl⟩
    refine ⟨f r, ?_⟩
    rw [smul_vec, smul_vec, ← map_mul, ← map_mul]
    funext i; fin_cases i <;> simp
  · rintro ⟨r', rfl⟩
    obtain ⟨r, rfl⟩ := hf r'
    refine ⟨r • vec a b, ⟨r, rfl⟩, ?_⟩
    rw [smul_vec, smul_vec, ← map_mul, ← map_mul]
    funext i; fin_cases i <;> simp

end SpanVec

section Levels

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']

theorem coordEquiv_rTensor (f : B →ₐ[𝒪] B') (y : latticeBaseChange 𝒪 K B (stdFullLattice K)) :
    coordEquiv K B' (LinearMap.rTensor _ f.toLinearMap y) = fun i => f (coordEquiv (𝒪 := 𝒪) K B y i) := by
  induction y using TensorProduct.induction_on with
  | zero => funext i; simp
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb]
    funext i
    simp only [Pi.add_apply, map_add]
  | tmul b v =>
    funext i
    rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, coordEquiv, coordEquiv, Module.Basis.equivFun_apply,
      Module.Basis.baseChange_repr_tmul, Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul, map_smul]

theorem coe_map_coordEquiv_lineBaseChange (f : B →ₐ[𝒪] B') (N : Submodule B (latticeBaseChange 𝒪 K B (stdFullLattice K))) :
    ((lineBaseChange f (stdFullLattice K) N).map (coordEquiv (𝒪 := 𝒪) K B').toLinearMap : Set (Fin 2 → B')) =
      Submodule.span B' ((fun w : Fin 2 → B => fun i => f (w i)) '' (N.map (coordEquiv (𝒪 := 𝒪) K B).toLinearMap)) := by
  rw [lineBaseChange, Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  have himg : (fun n => (coordEquiv (𝒪 := 𝒪) K B').toLinearMap (LinearMap.rTensor _ f.toLinearMap n)) '' (N : Set _) =
      (fun n => fun i => f ((coordEquiv (𝒪 := 𝒪) K B).toLinearMap n i)) '' (N : Set _) :=
    Set.image_congr fun n _ => by simp only [LinearEquiv.coe_coe]; exact coordEquiv_rTensor f n
  rw [himg]

variable {R : Type} [CommRing R] [Algebra 𝒪 R]

noncomputable def lineCoord (x : AdicPoint K π R) (n : ℕ) : Submodule (modPow π R n) (Fin 2 → modPow π R n) :=
  ((x.pt n).line (stdFullLattice K)).map (coordEquiv (𝒪 := 𝒪) K (modPow π R n)).toLinearMap

theorem invertible_lineCoord (x : AdicPoint K π R) (n : ℕ) :
    Module.Invertible (modPow π R n) ((Fin 2 → modPow π R n) ⧸ lineCoord x n) := by
  haveI := (x.pt n).invertible (stdFullLattice K)
  exact Module.Invertible.congr (Submodule.Quotient.equiv _ _ (coordEquiv (𝒪 := 𝒪) K (modPow π R n)) rfl)

theorem mem_stdLine_iff_lineCoord (x : AdicPoint K π R) (u : Fin 2 → R) :
    u ∈ x.stdLine ↔ ∀ n, (fun i => Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) (u i)) ∈ lineCoord x n := by
  rw [AdicPoint.mem_stdLine_iff]
  refine forall_congr' fun n => ?_
  rw [lineCoord, ← coordEquiv_coordToTensor K π R n u, Submodule.mem_map]
  constructor
  · intro h; exact ⟨_, h, rfl⟩
  · rintro ⟨y, hy, hyu⟩
    rw [LinearEquiv.coe_coe] at hyu
    rwa [← (coordEquiv (𝒪 := 𝒪) K (modPow π R n)).injective hyu]

theorem coe_lineCoord_eq_span_image (x : AdicPoint K π R) (n : ℕ) :
    (lineCoord x n : Set (Fin 2 → modPow π R n)) =
      Submodule.span (modPow π R n)
        ((fun w : Fin 2 → modPow π R (n + 1) => fun i => modPowTransition π R n (w i)) '' (lineCoord x (n + 1))) := by
  rw [lineCoord, lineCoord, ← x.compat n]
  exact coe_map_coordEquiv_lineBaseChange (modPowTransition π R n) ((x.pt (n + 1)).line (stdFullLattice K))

end Levels

section Sequence

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪}
variable {R : Type} [CommRing R] [Algebra 𝒪 R]

theorem modPowTransition_mk (n : ℕ) (r : R) :
    modPowTransition π R n (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) r := rfl

theorem modPowTransition_surjective (n : ℕ) : Function.Surjective (modPowTransition π R n) :=
  Ideal.Quotient.factor_surjective (span_pow_succ_le π R n)

theorem isUnit_of_isUnit_modPowTransition (n : ℕ) (c : modPow π R (n + 1))
    (h : IsUnit (modPowTransition π R n c)) : IsUnit c := by
  obtain ⟨d', hd'⟩ := h.exists_right_inv
  obtain ⟨d, rfl⟩ := modPowTransition_surjective (π := π) (R := R) n d'
  rw [← map_mul] at hd'
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (c * d)
  have hk : IsNilpotent (c * d - 1) := by
    rw [← hr] at hd' ⊢
    rw [modPowTransition_mk, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq, Ideal.mem_span_singleton] at hd'
    obtain ⟨s, hs⟩ := hd'
    refine ⟨2, ?_⟩
    rw [← map_one (Ideal.Quotient.mk _), ← map_sub, ← map_pow, hs, Ideal.Quotient.eq_zero_iff_mem]
    have : (algebraMap 𝒪 R π ^ (n + 1) * s) ^ 2 = algebraMap 𝒪 R π ^ (n + 1 + 1) * (algebraMap 𝒪 R π ^ n * s ^ 2) := by
      ring
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  have hu : IsUnit (c * d) := by
    have := hk.isUnit_one_add
    rwa [add_sub_cancel] at this
  exact isUnit_of_mul_isUnit_left hu

theorem lineCoord_eq_of_succ (x : AdicPoint K π R) (n : ℕ) (a b : modPow π R (n + 1))
    (h : lineCoord x (n + 1) = Submodule.span _ {vec a b}) :
    lineCoord x n = Submodule.span _ {vec (modPowTransition π R n a) (modPowTransition π R n b)} := by
  apply SetLike.coe_injective
  rw [coe_lineCoord_eq_span_image, h, image_span_vec (modPowTransition π R n) (modPowTransition_surjective n) a b,
    Submodule.span_eq]

end Sequence

section Limit

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪}
  {C : Type} [Field C] [Algebra K C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]
  {ϖ : PseudoUniformizer K C}

theorem typeAt (hF : IsAdicFrame π ϖ R) (x : AdicPoint K π R) (n : ℕ) :
    (∃ c, lineCoord x n = Submodule.span _ {vec c 1}) ∨ (∃ c, lineCoord x n = Submodule.span _ {vec 1 c}) := by
  haveI := isLocalRing_modPow hF n
  haveI := invertible_lineCoord x n
  rcases exists_eq_span_of_invertible (lineCoord x n) with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem typeII_desc (x : AdicPoint K π R) (n : ℕ) (h : ∃ c, lineCoord x (n + 1) = Submodule.span _ {vec c 1}) :
    ∃ c, lineCoord x n = Submodule.span _ {vec c 1} := by
  obtain ⟨c, hc⟩ := h
  refine ⟨modPowTransition π R n c, ?_⟩
  have := lineCoord_eq_of_succ x n c 1 hc
  rwa [map_one] at this

theorem typeII_desc_zero (x : AdicPoint K π R) (n : ℕ) (h : ∃ c, lineCoord x n = Submodule.span _ {vec c 1}) :
    ∃ c, lineCoord x 0 = Submodule.span _ {vec c 1} := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih (typeII_desc x n h)

theorem typeII_all (hF : IsAdicFrame π ϖ R) (x : AdicPoint K π R) (h0 : ∃ c, lineCoord x 0 = Submodule.span _ {vec c 1}) :
    ∀ n, ∃ c, lineCoord x n = Submodule.span _ {vec c 1} := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    rcases typeAt hF x (n + 1) with h | ⟨c, hc⟩
    · exact h
    · obtain ⟨cn, hcn⟩ := ih
      have h' := lineCoord_eq_of_succ x n 1 c hc
      rw [map_one, hcn] at h'
      have hu : IsUnit (modPowTransition π R n c) :=
        isUnit_of_mul_isUnit_right ((mul_eq_one_of_span_eq h'.symm).symm ▸ isUnit_one)
      have hcu := isUnit_of_isUnit_modPowTransition n c hu
      refine ⟨↑hcu.unit⁻¹, ?_⟩
      rw [hc, ← span_vec_unit' hcu.unit, IsUnit.unit_spec]

theorem typeI_all (hF : IsAdicFrame π ϖ R) (x : AdicPoint K π R) (h0 : ¬ ∃ c, lineCoord x 0 = Submodule.span _ {vec c 1}) :
    ∀ n, ∃ c, lineCoord x n = Submodule.span _ {vec 1 c} := by
  intro n
  rcases typeAt hF x n with h | h
  · exact absurd (typeII_desc_zero x n h) h0
  · exact h

theorem exists_lift (hF : IsAdicFrame π ϖ R) (c : ∀ n, modPow π R n)
    (hc : ∀ n, modPowTransition π R n (c (n + 1)) = c n) :
    ∃ L : R, ∀ n, Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) L = c n := by
  haveI := hF.complete
  choose ct hct using fun n => Ideal.Quotient.mk_surjective (c n)
  have hstep : ∀ n, ct (n + 1) - ct n ∈ Ideal.span {algebraMap 𝒪 R π ^ (n + 1)} := by
    intro n
    rw [← Ideal.Quotient.eq, hct n, ← hc n, ← hct (n + 1)]
    rfl
  have hchain : ∀ m n, m ≤ n → ct n - ct m ∈ Ideal.span {algebraMap 𝒪 R π ^ (m + 1)} := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => rw [sub_self]; exact zero_mem _
    | succ n hmn ih =>
      have : ct (n + 1) - ct m = (ct (n + 1) - ct n) + (ct n - ct m) := by ring
      rw [this]
      refine add_mem (Ideal.span_singleton_le_span_singleton.mpr ?_ (hstep n)) ih
      exact pow_dvd_pow _ (Nat.succ_le_succ hmn)
  have hI : ∀ m : ℕ, (Ideal.span {algebraMap 𝒪 R π} ^ m • ⊤ : Submodule R R) = Ideal.span {algebraMap 𝒪 R π ^ m} := by
    intro m
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {algebraMap 𝒪 R π}) ct (fun {m n} hmn => by
    rw [SModEq.sub_mem, hI]
    have := hchain m n hmn
    rw [← neg_sub, neg_mem_iff]
    exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ m)) this)
  refine ⟨L, fun n => ?_⟩
  rw [← hct n, Ideal.Quotient.eq]
  have h1 : ct (n + 1) - L ∈ Ideal.span {algebraMap 𝒪 R π ^ (n + 1)} := by
    have := hL (n + 1); rwa [SModEq.sub_mem, hI] at this
  have : L - ct n = (ct (n + 1) - ct n) - (ct (n + 1) - L) := by ring
  rw [this]
  exact sub_mem (hstep n) h1

theorem eq_zero_of_forall_mem (hF : IsAdicFrame π ϖ R) (d : R)
    (hd : ∀ n, d ∈ Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) : d = 0 := by
  haveI := hF.complete
  refine IsHausdorff.haus' (I := Ideal.span {algebraMap 𝒪 R π}) d fun n => ?_
  rw [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ n)) (hd n)

theorem stdLine_eq_span_II (hF : IsAdicFrame π ϖ R) (x : AdicPoint K π R) (L : R)
    (hL : ∀ n, lineCoord x n = Submodule.span _ {vec (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) L) 1}) :
    x.stdLine = Submodule.span R {vec L 1} := by
  ext u
  rw [mem_stdLine_iff_lineCoord, mem_span_vec_one_iff']
  simp only [hL, mem_span_vec_one_iff', ← map_mul, Ideal.Quotient.eq]
  constructor
  · intro h
    rw [← sub_eq_zero]
    exact eq_zero_of_forall_mem hF _ h
  · intro h n
    rw [h, sub_self]; exact zero_mem _

theorem stdLine_eq_span_I (hF : IsAdicFrame π ϖ R) (x : AdicPoint K π R) (L : R)
    (hL : ∀ n, lineCoord x n = Submodule.span _ {vec 1 (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) L)}) :
    x.stdLine = Submodule.span R {vec 1 L} := by
  ext u
  rw [mem_stdLine_iff_lineCoord, mem_span_vec_one_iff]
  simp only [hL, mem_span_vec_one_iff, ← map_mul, Ideal.Quotient.eq]
  constructor
  · intro h
    rw [← sub_eq_zero]
    exact eq_zero_of_forall_mem hF _ h
  · intro h n
    rw [h, sub_self]; exact zero_mem _

end Limit

section Bounds

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}

theorem algebraMap_ne_zero' (hπ : Irreducible π) : algebraMap 𝒪 K π ≠ 0 :=
  fun h => hπ.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective 𝒪 K)).mp h)

theorem exists_pow_isInteger (hπ : Irreducible π) (s : Finset K) :
    ∃ k : ℕ, ∀ c ∈ s, IsLocalization.IsInteger 𝒪 (algebraMap 𝒪 K (π ^ k) * c) := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors 𝒪) s id
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero b.2) hπ
  refine ⟨k, fun c hc => ?_⟩
  have := hb c hc
  rw [id, Algebra.smul_def, hu, map_mul, mul_assoc] at this
  obtain ⟨r, hr⟩ := this
  refine ⟨↑u⁻¹ * r, ?_⟩
  rw [map_mul, hr, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

theorem isInteger_pow_mul_of_le {c : K} {k k' : ℕ} (hk : k ≤ k')
    (h : IsLocalization.IsInteger 𝒪 (algebraMap 𝒪 K (π ^ k) * c)) :
    IsLocalization.IsInteger 𝒪 (algebraMap 𝒪 K (π ^ k') * c) := by
  obtain ⟨r, hr⟩ := h
  refine ⟨π ^ (k' - k) * r, ?_⟩
  rw [map_mul, hr, ← mul_assoc, ← map_mul, ← pow_add, Nat.sub_add_cancel hk]

theorem exists_pow_isInteger_apply (hπ : Irreducible π) (M : FullLattice 𝒪 K) :
    ∃ k : ℕ, ∀ v ∈ M.1, ∀ i, IsLocalization.IsInteger 𝒪 (algebraMap 𝒪 K (π ^ k) * v i) := by
  classical
  obtain ⟨S, hS⟩ := M.2.1
  obtain ⟨k, hk⟩ := exists_pow_isInteger (K := K) hπ (S.biUnion fun v => {v 0, v 1})
  refine ⟨k, fun v hv => ?_⟩
  rw [← hS] at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    intro i
    apply hk
    rw [Finset.mem_biUnion]
    refine ⟨w, hw, ?_⟩
    fin_cases i <;> simp
  | zero => intro i; rw [Pi.zero_apply, mul_zero]; exact IsLocalization.isInteger_zero
  | add a b _ _ ha hb => intro i; rw [Pi.add_apply, mul_add]; exact IsLocalization.isInteger_add (ha i) (hb i)
  | smul r a _ ha =>
    intro i
    rw [Pi.smul_apply, Algebra.smul_def, mul_left_comm]
    exact IsLocalization.isInteger_mul ⟨r, rfl⟩ (ha i)

theorem exists_pow_smul_single_mem (hπ : Irreducible π) (M : FullLattice 𝒪 K) (i : Fin 2) :
    ∃ k : ℕ, algebraMap 𝒪 K (π ^ k) • (Pi.single i 1 : Fin 2 → K) ∈ M.1 := by
  classical
  have hmem : (Pi.single i 1 : Fin 2 → K) ∈ Submodule.span K (M.1 : Set (Fin 2 → K)) := by
    rw [M.2.2]; exact Submodule.mem_top
  obtain ⟨c, hc, hsum⟩ := Submodule.mem_span_set.mp hmem
  obtain ⟨k, hk⟩ := exists_pow_isInteger (K := K) hπ (c.support.image c)
  refine ⟨k, ?_⟩
  rw [← hsum, Finsupp.sum, Finset.smul_sum]
  refine Submodule.sum_mem _ fun w hw => ?_
  rw [smul_smul]
  obtain ⟨r, hr⟩ := hk (c w) (Finset.mem_image_of_mem c hw)
  rw [← hr, algebraMap_smul]
  exact Submodule.smul_mem _ r (hc (Finset.mem_coe.mpr hw))

theorem pow_smul_single_mem_of_le (M : FullLattice 𝒪 K) (i : Fin 2) {k k' : ℕ} (hk : k ≤ k')
    (h : algebraMap 𝒪 K (π ^ k) • (Pi.single i 1 : Fin 2 → K) ∈ M.1) :
    algebraMap 𝒪 K (π ^ k') • (Pi.single i 1 : Fin 2 → K) ∈ M.1 := by
  have : algebraMap 𝒪 K (π ^ k') • (Pi.single i 1 : Fin 2 → K) =
      (π ^ (k' - k)) • (algebraMap 𝒪 K (π ^ k) • (Pi.single i 1 : Fin 2 → K)) := by
    rw [algebraMap_smul, algebraMap_smul, smul_smul, ← pow_add, Nat.sub_add_cancel hk]
  rw [this]
  exact Submodule.smul_mem _ _ h

end Bounds

section Primitive

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}

noncomputable def scaledE0 (π : 𝒪) (A t : ℕ) : Fin 2 → K :=
  (algebraMap 𝒪 K (π ^ t) * (algebraMap 𝒪 K (π ^ A))⁻¹) • (Pi.single 0 1 : Fin 2 → K)

theorem scaledE0_two_mul (hπ : Irreducible π) (A : ℕ) :
    scaledE0 (K := K) π A (2 * A) = algebraMap 𝒪 K (π ^ A) • (Pi.single 0 1 : Fin 2 → K) := by
  have hne : algebraMap 𝒪 K (π ^ A) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ (algebraMap_ne_zero' hπ)
  rw [scaledE0, two_mul, pow_add, map_mul, mul_assoc, mul_inv_cancel₀ hne, mul_one]

theorem pow_smul_scaledE0 (hπ : Irreducible π) (A t : ℕ) (ht : t ≤ 2 * A) :
    (π ^ (2 * A - t)) • scaledE0 (K := K) π A t = algebraMap 𝒪 K (π ^ A) • (Pi.single 0 1 : Fin 2 → K) := by
  rw [← algebraMap_smul K (π ^ (2 * A - t)), ← scaledE0_two_mul hπ A, scaledE0, scaledE0, smul_smul, ← mul_assoc,
    ← map_mul, ← pow_add, Nat.sub_add_cancel ht]

theorem pi_smul_scaledE0_succ (hπ : Irreducible π) (A t : ℕ) :
    algebraMap 𝒪 K π • scaledE0 (K := K) π A t = scaledE0 (K := K) π A (t + 1) := by
  rw [scaledE0, scaledE0, smul_smul, ← mul_assoc, ← map_mul, ← pow_succ']

noncomputable def primIdx (hπ : Irreducible π) (M : FullLattice 𝒪 K) (A : ℕ)
    (hlow : algebraMap 𝒪 K (π ^ A) • (Pi.single 0 1 : Fin 2 → K) ∈ M.1) : ℕ := by
  classical
  exact Nat.find (⟨2 * A, by rw [scaledE0_two_mul hπ]; exact hlow⟩ : ∃ t, scaledE0 (K := K) π A t ∈ M.1)

theorem scaledE0_primIdx_mem (hπ : Irreducible π) (M : FullLattice 𝒪 K) (A : ℕ)
    (hlow : algebraMap 𝒪 K (π ^ A) • (Pi.single 0 1 : Fin 2 → K) ∈ M.1) :
    scaledE0 (K := K) π A (primIdx hπ M A hlow) ∈ M.1 := by
  classical
  exact Nat.find_spec (⟨2 * A, by rw [scaledE0_two_mul hπ]; exact hlow⟩ : ∃ t, scaledE0 (K := K) π A t ∈ M.1)

theorem primIdx_le (hπ : Irreducible π) (M : FullLattice 𝒪 K) (A : ℕ)
    (hlow : algebraMap 𝒪 K (π ^ A) • (Pi.single 0 1 : Fin 2 → K) ∈ M.1) :
    primIdx hπ M A hlow ≤ 2 * A := by
  classical
  exact Nat.find_min' _ (by rw [scaledE0_two_mul hπ]; exact hlow)

theorem primIdx_min (hπ : Irreducible π) (M : FullLattice 𝒪 K) (A : ℕ)
    (hlow : algebraMap 𝒪 K (π ^ A) • (Pi.single 0 1 : Fin 2 → K) ∈ M.1) {t : ℕ} (ht : t < primIdx hπ M A hlow) :
    scaledE0 (K := K) π A t ∉ M.1 := by
  classical
  exact Nat.find_min _ ht

theorem scaledE0_primIdx_not_div (hπ : Irreducible π) (M : FullLattice 𝒪 K) (A : ℕ)
    (hlow : algebraMap 𝒪 K (π ^ A) • (Pi.single 0 1 : Fin 2 → K) ∈ M.1)
    (hup : ∀ v ∈ M.1, ∀ i, IsLocalization.IsInteger 𝒪 (algebraMap 𝒪 K (π ^ A) * v i)) :
    ¬ ∃ w : ↥M.1, scaledE0 (K := K) π A (primIdx hπ M A hlow) = algebraMap 𝒪 K π • (w : Fin 2 → K) := by
  rintro ⟨w, hw⟩
  have hπK : algebraMap 𝒪 K π ≠ 0 := algebraMap_ne_zero' hπ
  by_cases h0 : primIdx hπ M A hlow = 0
  ·
    have hA : algebraMap 𝒪 K (π ^ A) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hπK
    have hw0 : algebraMap 𝒪 K (π ^ A) * (w : Fin 2 → K) 0 = (algebraMap 𝒪 K π)⁻¹ := by
      have h' := congrFun hw 0
      rw [h0, scaledE0, pow_zero, map_one, one_mul, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
        mul_one, smul_eq_mul] at h'

      have hw' : (w : Fin 2 → K) 0 = (algebraMap 𝒪 K π)⁻¹ * (algebraMap 𝒪 K (π ^ A))⁻¹ := by
        calc (w : Fin 2 → K) 0 = (algebraMap 𝒪 K π)⁻¹ * (algebraMap 𝒪 K π * (w : Fin 2 → K) 0) := by
              rw [← mul_assoc, inv_mul_cancel₀ hπK, one_mul]
          _ = (algebraMap 𝒪 K π)⁻¹ * (algebraMap 𝒪 K (π ^ A))⁻¹ := by rw [← h']
      rw [hw', mul_left_comm, mul_inv_cancel₀ hA, mul_one]
    obtain ⟨r, hr⟩ := hup w w.2 0
    rw [hw0] at hr
    have : algebraMap 𝒪 K (r * π) = 1 := by rw [map_mul, hr, inv_mul_cancel₀ hπK]
    have h1 : r * π = 1 := (IsFractionRing.injective 𝒪 K) (by rw [this, map_one])
    have hu : IsUnit (r * π) := by rw [h1]; exact isUnit_one
    exact hπ.not_isUnit (isUnit_of_mul_isUnit_right hu)
  ·
    obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero h0
    apply primIdx_min hπ M A hlow (show t < primIdx hπ M A hlow by omega)
    have : (w : Fin 2 → K) = scaledE0 (K := K) π A t := by
      apply smul_right_injective (Fin 2 → K) hπK
      show algebraMap 𝒪 K π • (w : Fin 2 → K) = algebraMap 𝒪 K π • scaledE0 (K := K) π A t
      rw [← hw, pi_smul_scaledE0_succ hπ, ht]
    rw [← this]; exact w.2

end Primitive

section Key

open CerednikDrinfeld.FormalOmega.LevelAux

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}
  {C : Type} [Field C] [Algebra K C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]
  {ϖ : PseudoUniformizer K C}

theorem smul_mem_of_mem_stdLattice (M : FullLattice 𝒪 K) (c : K)
    (h0 : c • (Pi.single 0 1 : Fin 2 → K) ∈ M.1) (h1 : c • (Pi.single 1 1 : Fin 2 → K) ∈ M.1)
    (v : Fin 2 → K) (hv : v ∈ stdLattice 𝒪 K) : c • v ∈ M.1 := by
  rw [mem_stdLattice] at hv
  obtain ⟨r0, hr0⟩ := hv 0
  obtain ⟨r1, hr1⟩ := hv 1
  have : v = r0 • (Pi.single 0 1 : Fin 2 → K) + r1 • (Pi.single 1 1 : Fin 2 → K) := by
    funext j
    fin_cases j <;> simp [Pi.single_apply, ← hr0, ← hr1, Algebra.smul_def]
  rw [this, smul_add, smul_comm c r0, smul_comm c r1]
  exact add_mem (Submodule.smul_mem _ _ h0) (Submodule.smul_mem _ _ h1)

theorem one_tmul_pow_smul_single_mem (hπ : Irreducible π) {B : Type} [CommRing B] [Algebra 𝒪 B]
    (d : DeligneDatum (K := K) π B)
    (h0 : (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 ∈ d.line (stdFullLattice K)) (M : FullLattice 𝒪 K) (A : ℕ)
    (hl0 : algebraMap 𝒪 K (π ^ A) • (Pi.single 0 1 : Fin 2 → K) ∈ M.1)
    (hl1 : algebraMap 𝒪 K (π ^ A) • (Pi.single 1 1 : Fin 2 → K) ∈ M.1) :
    (1 : B) ⊗ₜ[𝒪] (⟨algebraMap 𝒪 K (π ^ A) • (Pi.single 0 1 : Fin 2 → K), hl0⟩ : ↥M.1) ∈ d.line M := by
  have hne : algebraMap 𝒪 K (π ^ A) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ (algebraMap_ne_zero' hπ)
  set c : Kˣ := Units.mk0 _ hne with hc

  have h1 : actBaseChange B (scalarGL c) (stdFullLattice K) ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0) ∈
      d.line (FullLattice.act (scalarGL c) (stdFullLattice K)) := by
    rw [d.homothety c (stdFullLattice K)]
    exact Submodule.mem_map_of_mem h0
  rw [actBaseChange_tmul] at h1

  have hle : (FullLattice.act (scalarGL c) (stdFullLattice K)).1 ≤ M.1 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [mulVecLinR_apply, scalarGL_mulVec]
    exact smul_mem_of_mem_stdLattice M _ hl0 hl1 v hv
  have h2 := d.mono hle (Submodule.mem_map_of_mem (f := inclBaseChange B hle) h1)
  have key : inclBaseChange B hle ((1 : B) ⊗ₜ[𝒪] (latticeMapEquiv (scalarGL c) _ (stdBasisVec (𝒪 := 𝒪) K 0))) =
      (1 : B) ⊗ₜ[𝒪] (⟨algebraMap 𝒪 K (π ^ A) • (Pi.single 0 1 : Fin 2 → K), hl0⟩ : ↥M.1) := by
    show (1 : B) ⊗ₜ[𝒪] (Submodule.inclusion hle (latticeMapEquiv (scalarGL c) _ (stdBasisVec (𝒪 := 𝒪) K 0))) = _
    congr 1
    apply Subtype.ext
    show Matrix.mulVec ((scalarGL c : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
        (Pi.single 0 1 : Fin 2 → K) = algebraMap 𝒪 K (π ^ A) • (Pi.single 0 1 : Fin 2 → K)
    rw [scalarGL_mulVec]; rfl
  rw [← key]
  exact h2

theorem pow_not_mem_span_pow (hF : IsAdicFrame π ϖ R) {j n : ℕ} (hj : j ≤ n) :
    algebraMap 𝒪 R π ^ j ∉ Ideal.span {algebraMap 𝒪 R π ^ (n + 1)} := by
  intro h
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨s, hs⟩ := h
  apply pi_mem_nonunits hF

  have hπC : algebraMap R C (algebraMap 𝒪 R π) ≠ 0 := by
    rw [← IsScalarTower.algebraMap_apply]; intro h0
    have := hF.v_algebraMap_pos; rw [h0, map_zero] at this; exact lt_irrefl _ this
  have : algebraMap R C (1 - algebraMap 𝒪 R π ^ (n + 1 - j) * s) = 0 := by
    have h' := congrArg (algebraMap R C) hs
    rw [map_mul, show n + 1 = j + (n + 1 - j) by omega, pow_add, map_mul, mul_assoc] at h'
    have h'' : algebraMap R C (algebraMap 𝒪 R π ^ j) * (1 - algebraMap R C (algebraMap 𝒪 R π ^ (n + 1 - j) * s)) = 0 := by
      rw [mul_sub, mul_one, map_mul, sub_eq_zero]; exact h'
    rcases mul_eq_zero.mp h'' with h3 | h3
    · rw [map_pow] at h3; exact absurd h3 (pow_ne_zero j hπC)
    · rw [map_sub, map_one]; exact h3
  have h4 : 1 - algebraMap 𝒪 R π ^ (n + 1 - j) * s = 0 := hF.injective (by rw [this, map_zero])
  rw [sub_eq_zero] at h4
  refine isUnit_of_dvd_one ⟨algebraMap 𝒪 R π ^ (n - j) * s, ?_⟩
  rw [h4, show n + 1 - j = (n - j) + 1 by omega, pow_succ]; ring

end Key

section Key2

open CerednikDrinfeld.FormalOmega.LevelAux

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}
  {C : Type} [Field C] [Algebra K C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]
  {ϖ : PseudoUniformizer K C}

theorem isUnit_of_isUnit_red (n : ℕ) (b : modPow π R n) (h : IsUnit (red (R := R) π n b)) : IsUnit b := by
  induction n with
  | zero => rwa [red_zero_eq_id] at h
  | succ n ih =>
    rw [red_succ] at h
    exact isUnit_of_isUnit_modPowTransition n b (ih _ h)

theorem mem_sup_of_pow_smul_mem (hF : IsAdicFrame π ϖ R) (n : ℕ) (d : DeligneDatum (K := K) π (modPow π R n))
    (M : FullLattice 𝒪 K) (y : latticeBaseChange 𝒪 K (modPow π R n) M) (j : ℕ) (hj : j ≤ n)
    (hy : (algebraMap 𝒪 (modPow π R n) (π ^ j)) • y ∈ d.line M)
    (𝔮 : Ideal (modPow π R n)) (hq : ∀ b, b ∉ 𝔮 → IsUnit b) :
    y ∈ d.line M ⊔ (𝔮 • ⊤ : Submodule (modPow π R n) (latticeBaseChange 𝒪 K (modPow π R n) M)) := by
  by_contra hnot
  haveI := isLocalRing_modPow hF n
  haveI := d.invertible M
  set N := d.line M with hN
  obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv.mp
    (inferInstance : Module.Free (modPow π R n) (latticeBaseChange 𝒪 K (modPow π R n) M ⧸ N))
  have h1 : (algebraMap 𝒪 (modPow π R n) (π ^ j)) • N.mkQ y = 0 := by
    rw [← map_smul]; exact (Submodule.Quotient.mk_eq_zero N).mpr hy
  have h2 : algebraMap 𝒪 (modPow π R n) (π ^ j) * e (N.mkQ y) = 0 := by
    rw [← smul_eq_mul, ← map_smul, h1, map_zero]
  have hb : e (N.mkQ y) ∉ 𝔮 := by
    intro hb
    apply hnot
    have hq' : N.mkQ y ∈ (𝔮 • ⊤ : Submodule (modPow π R n) (_ ⧸ N)) := by
      have : N.mkQ y = e (N.mkQ y) • e.symm 1 := by
        rw [← LinearEquiv.map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
      rw [this]
      exact Submodule.smul_mem_smul hb Submodule.mem_top
    have : y ∈ ((𝔮 • ⊤ : Submodule (modPow π R n) (latticeBaseChange 𝒪 K (modPow π R n) M)).map N.mkQ).comap N.mkQ := by
      rw [Submodule.mem_comap, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]; exact hq'
    rwa [Submodule.comap_map_mkQ] at this
  have hu := hq _ hb
  have hzero : algebraMap 𝒪 (modPow π R n) (π ^ j) = 0 := by
    have := congrArg (fun z => z * (↑hu.unit⁻¹ : modPow π R n)) h2
    simpa only [mul_assoc, IsUnit.mul_val_inv, mul_one, zero_mul] using this
  apply pow_not_mem_span_pow hF hj
  rw [IsScalarTower.algebraMap_apply 𝒪 R (modPow π R n), map_pow, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem] at hzero
  exact hzero

theorem one_tmul_eq_smul (M : FullLattice 𝒪 K) {B : Type} [CommRing B] [Algebra 𝒪 B] (f g : Fin 2 → K) (hf : f ∈ M.1)
    (hg : g ∈ M.1) (j : ℕ) (h : (π ^ j) • f = g) :
    (1 : B) ⊗ₜ[𝒪] (⟨g, hg⟩ : ↥M.1) = (algebraMap 𝒪 B (π ^ j)) • ((1 : B) ⊗ₜ[𝒪] (⟨f, hf⟩ : ↥M.1)) := by
  have : (⟨g, hg⟩ : ↥M.1) = (π ^ j) • (⟨f, hf⟩ : ↥M.1) := Subtype.ext (by rw [Submodule.coe_smul, h])
  rw [this, TensorProduct.tmul_smul, algebraMap_smul]

theorem not_forall_one_tmul_single_mem (hF : IsAdicFrame π ϖ R) (x : AdicPoint K π R)
    (h : ∀ n, (1 : modPow π R n) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 ∈ (x.pt n).line (stdFullLattice K)) : False := by
  have hπ := hF.irreducible
  haveI := isLocalRing_modPow hF 0
  set 𝔪₀ := IsLocalRing.maximalIdeal (modPow π R 0) with h𝔪₀
  obtain ⟨M', M, hle, hπM, h1, h2⟩ := (x.pt 0).nondeg 𝔪₀ (IsLocalRing.maximalIdeal.isMaximal _).isPrime

  obtain ⟨kup, hkup⟩ := exists_pow_isInteger_apply (K := K) hπ M
  obtain ⟨k0, hk0⟩ := exists_pow_smul_single_mem (K := K) hπ M' 0
  obtain ⟨k1, hk1⟩ := exists_pow_smul_single_mem (K := K) hπ M' 1
  set A := kup + k0 + k1 with hA
  have hl0' := pow_smul_single_mem_of_le M' 0 (show k0 ≤ A by omega) hk0
  have hl1' := pow_smul_single_mem_of_le M' 1 (show k1 ≤ A by omega) hk1
  have hl0 : algebraMap 𝒪 K (π ^ A) • (Pi.single 0 1 : Fin 2 → K) ∈ M.1 := hle hl0'
  have hl1 : algebraMap 𝒪 K (π ^ A) • (Pi.single 1 1 : Fin 2 → K) ∈ M.1 := hle hl1'
  have hup : ∀ v ∈ M.1, ∀ i, IsLocalization.IsInteger 𝒪 (algebraMap 𝒪 K (π ^ A) * v i) :=
    fun v hv i => isInteger_pow_mul_of_le (show kup ≤ A by omega) (hkup v hv i)

  set n := 2 * A with hn
  have hE : (x.pt 0).EdgeNondegAt π 𝔪₀ M' M := ⟨hle, hπM, h1, h2⟩
  rw [← map_red_pt x n, edgeNondegAt_map_iff (red π n) (red_surjective π n)] at hE
  obtain ⟨_, _, h1n, h2n⟩ := hE
  set 𝔮 := Ideal.comap (red (R := R) π n) 𝔪₀ with h𝔮
  have hq : ∀ b, b ∉ 𝔮 → IsUnit b := by
    intro b hb
    apply isUnit_of_isUnit_red n b
    rw [h𝔮, Ideal.mem_comap, h𝔪₀, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hb
    exact hb

  set t₀ := primIdx hπ M A hl0 with ht₀
  set f := scaledE0 (K := K) π A t₀ with hf
  have hfM : f ∈ M.1 := scaledE0_primIdx_mem hπ M A hl0
  have hfA : (π ^ (2 * A - t₀)) • f = algebraMap 𝒪 K (π ^ A) • (Pi.single 0 1 : Fin 2 → K) :=
    pow_smul_scaledE0 hπ A t₀ (primIdx_le hπ M A hl0)
  have hj : 2 * A - t₀ ≤ n := Nat.sub_le _ _

  have hmemM := mem_sup_of_pow_smul_mem hF n (x.pt n) M ((1 : modPow π R n) ⊗ₜ[𝒪] (⟨f, hfM⟩ : ↥M.1)) _ hj
    (by rw [← one_tmul_eq_smul M f _ hfM hl0 _ hfA]; exact one_tmul_pow_smul_single_mem hπ (x.pt n) (h n) M A hl0 hl1)
    𝔮 hq
  have hfM' : f ∈ M'.1 := by
    by_contra hf'
    exact h1n ⟨f, hfM⟩ hf' hmemM

  have hmemM' := mem_sup_of_pow_smul_mem hF n (x.pt n) M' ((1 : modPow π R n) ⊗ₜ[𝒪] (⟨f, hfM'⟩ : ↥M'.1)) _ hj
    (by rw [← one_tmul_eq_smul M' f _ hfM' hl0' _ hfA]; exact one_tmul_pow_smul_single_mem hπ (x.pt n) (h n) M' A hl0' hl1')
    𝔮 hq
  exact h2n ⟨f, hfM'⟩ (scaledE0_primIdx_not_div hπ M A hl0 hup) hmemM'

end Key2

section Assembly

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪}
  {R : Type} [CommRing R] [Algebra 𝒪 R] {C : Type} [Field C] [Algebra R C]

theorem vec_one_zero_eq_single (n : ℕ) : (vec 1 0 : Fin 2 → modPow π R n) = Pi.single 0 1 := by
  simp [vec]

theorem vecLit_eq_vec (a b : C) : (![a, b] : Fin 2 → C) = vec a b := by
  funext j; fin_cases j <;> simp

theorem algebraMap_vec (a b : R) : (fun i => algebraMap R C (vec a b i)) = vec (algebraMap R C a) (algebraMap R C b) := by
  funext j; fin_cases j <;> simp

theorem lineC_eq_of_stdLine_eq (x : AdicPoint K π R) (v : Fin 2 → R) (hv : x.stdLine = Submodule.span R {v}) :
    x.lineC C = Submodule.span C {fun i => algebraMap R C (v i)} := by
  rw [AdicPoint.lineC, hv]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
    show (fun i => algebraMap R C ((r • v) i)) ∈ _
    have : (fun i => algebraMap R C ((r • v) i)) = algebraMap R C r • fun i => algebraMap R C (v i) := by
      funext i; simp [Algebra.smul_def]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨v, Submodule.mem_span_singleton_self v, rfl⟩

theorem one_tmul_single_mem_of_lineCoord (x : AdicPoint K π R) (n : ℕ)
    (h : lineCoord x n = Submodule.span (modPow π R n) {(vec 1 0 : Fin 2 → modPow π R n)}) :
    (1 : modPow π R n) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 ∈ (x.pt n).line (stdFullLattice K) := by
  have hmem : (vec 1 0 : Fin 2 → modPow π R n) ∈ lineCoord x n := h ▸ Submodule.mem_span_singleton_self _
  rw [lineCoord, Submodule.mem_map] at hmem
  obtain ⟨y, hy, hyv⟩ := hmem
  rw [LinearEquiv.coe_coe, vec_one_zero_eq_single n, ← coordEquiv_tmul (𝒪 := 𝒪) K (modPow π R n) (1 : modPow π R n) 0] at hyv
  rwa [(coordEquiv (𝒪 := 𝒪) K (modPow π R n)).injective hyv] at hy

end Assembly

end CerednikDrinfeld.FormalOmega.T2aAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane.CerednikDrinfeld.FormalOmega.T2aAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane.CerednikDrinfeld.FormalOmega"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane.CerednikDrinfeld"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.upperHalfPlane"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt modPow span_pow_succ_le modPowTransition AdicPoint stdFullLattice stdBasisVec coordToTensor AdicPoint.mem_stdLine_iff AdicPoint.lineC AdicPoint.vecCons_toOmega_mem coe_ofEq_apply actBaseChange_tmul rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum lineBaseChange"
namespace T2aAux
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

open TensorProduct CerednikDrinfeld.FormalOmega.LevelAux

section PrimitiveU

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}

noncomputable def scaledU (π : 𝒪) (A t : ℕ) (u : Fin 2 → K) : Fin 2 → K :=
  (algebraMap 𝒪 K (π ^ t) * (algebraMap 𝒪 K (π ^ A))⁻¹) • u

theorem scaledU_two_mul (hπ : Irreducible π) (A : ℕ) (u : Fin 2 → K) :
    scaledU π A (2 * A) u = algebraMap 𝒪 K (π ^ A) • u := by
  have hne : algebraMap 𝒪 K (π ^ A) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ (algebraMap_ne_zero' hπ)
  rw [scaledU, two_mul, pow_add, map_mul, mul_assoc, mul_inv_cancel₀ hne, mul_one]

theorem pow_smul_scaledU (hπ : Irreducible π) (A t : ℕ) (ht : t ≤ 2 * A) (u : Fin 2 → K) :
    (π ^ (2 * A - t)) • scaledU π A t u = algebraMap 𝒪 K (π ^ A) • u := by
  rw [← algebraMap_smul K (π ^ (2 * A - t)), ← scaledU_two_mul hπ A, scaledU, scaledU, smul_smul, ← mul_assoc,
    ← map_mul, ← pow_add, Nat.sub_add_cancel ht]

theorem pi_smul_scaledU_succ (A t : ℕ) (u : Fin 2 → K) :
    algebraMap 𝒪 K π • scaledU π A t u = scaledU π A (t + 1) u := by
  rw [scaledU, scaledU, smul_smul, ← mul_assoc, ← map_mul, ← pow_succ']

noncomputable def primIdxU (hπ : Irreducible π) (M : FullLattice 𝒪 K) (A : ℕ) (u : Fin 2 → K)
    (hlow : algebraMap 𝒪 K (π ^ A) • u ∈ M.1) : ℕ := by
  classical
  exact Nat.find (⟨2 * A, by rw [scaledU_two_mul hπ]; exact hlow⟩ : ∃ t, scaledU π A t u ∈ M.1)

theorem scaledU_primIdxU_mem (hπ : Irreducible π) (M : FullLattice 𝒪 K) (A : ℕ) (u : Fin 2 → K)
    (hlow : algebraMap 𝒪 K (π ^ A) • u ∈ M.1) : scaledU π A (primIdxU hπ M A u hlow) u ∈ M.1 := by
  classical
  exact Nat.find_spec (⟨2 * A, by rw [scaledU_two_mul hπ]; exact hlow⟩ : ∃ t, scaledU π A t u ∈ M.1)

theorem primIdxU_le (hπ : Irreducible π) (M : FullLattice 𝒪 K) (A : ℕ) (u : Fin 2 → K)
    (hlow : algebraMap 𝒪 K (π ^ A) • u ∈ M.1) : primIdxU hπ M A u hlow ≤ 2 * A := by
  classical
  exact Nat.find_min' _ (by rw [scaledU_two_mul hπ]; exact hlow)

theorem primIdxU_min (hπ : Irreducible π) (M : FullLattice 𝒪 K) (A : ℕ) (u : Fin 2 → K)
    (hlow : algebraMap 𝒪 K (π ^ A) • u ∈ M.1) {t : ℕ} (ht : t < primIdxU hπ M A u hlow) :
    scaledU π A t u ∉ M.1 := by
  classical
  exact Nat.find_min _ ht

theorem scaledU_primIdxU_not_div (hπ : Irreducible π) (M : FullLattice 𝒪 K) (A : ℕ) (u : Fin 2 → K)
    (hlow : algebraMap 𝒪 K (π ^ A) • u ∈ M.1) (i₀ : Fin 2) (hi : u i₀ = 1)
    (hup : ∀ v ∈ M.1, ∀ i, IsLocalization.IsInteger 𝒪 (algebraMap 𝒪 K (π ^ A) * v i)) :
    ¬ ∃ w : ↥M.1, scaledU π A (primIdxU hπ M A u hlow) u = algebraMap 𝒪 K π • (w : Fin 2 → K) := by
  rintro ⟨w, hw⟩
  have hπK : algebraMap 𝒪 K π ≠ 0 := algebraMap_ne_zero' hπ
  by_cases h0 : primIdxU hπ M A u hlow = 0
  · have hA : algebraMap 𝒪 K (π ^ A) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hπK
    have hw0 : algebraMap 𝒪 K (π ^ A) * (w : Fin 2 → K) i₀ = (algebraMap 𝒪 K π)⁻¹ := by
      have h' := congrFun hw i₀
      rw [h0, scaledU, pow_zero, map_one, one_mul, Pi.smul_apply, Pi.smul_apply, hi, smul_eq_mul,
        mul_one, smul_eq_mul] at h'
      have hw' : (w : Fin 2 → K) i₀ = (algebraMap 𝒪 K π)⁻¹ * (algebraMap 𝒪 K (π ^ A))⁻¹ := by
        calc (w : Fin 2 → K) i₀ = (algebraMap 𝒪 K π)⁻¹ * (algebraMap 𝒪 K π * (w : Fin 2 → K) i₀) := by
              rw [← mul_assoc, inv_mul_cancel₀ hπK, one_mul]
          _ = (algebraMap 𝒪 K π)⁻¹ * (algebraMap 𝒪 K (π ^ A))⁻¹ := by rw [← h']
      rw [hw', mul_left_comm, mul_inv_cancel₀ hA, mul_one]
    obtain ⟨r, hr⟩ := hup w w.2 i₀
    rw [hw0] at hr
    have : algebraMap 𝒪 K (r * π) = 1 := by rw [map_mul, hr, inv_mul_cancel₀ hπK]
    have h1 : r * π = 1 := (IsFractionRing.injective 𝒪 K) (by rw [this, map_one])
    have hu : IsUnit (r * π) := by rw [h1]; exact isUnit_one
    exact hπ.not_isUnit (isUnit_of_mul_isUnit_right hu)
  · obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero h0
    apply primIdxU_min hπ M A u hlow (show t < primIdxU hπ M A u hlow by omega)
    have : (w : Fin 2 → K) = scaledU π A t u := by
      apply smul_right_injective (Fin 2 → K) hπK
      show algebraMap 𝒪 K π • (w : Fin 2 → K) = algebraMap 𝒪 K π • scaledU π A t u
      rw [← hw, pi_smul_scaledU_succ, ht]
    rw [← this]; exact w.2

end PrimitiveU
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane.CerednikDrinfeld.FormalOmega.T2aAux"

section KeyU

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}
  {C : Type} [Field C] [Algebra K C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]
  {ϖ : PseudoUniformizer K C}

theorem one_tmul_pow_smul_mem (hπ : Irreducible π) {B : Type} [CommRing B] [Algebra 𝒪 B]
    (d : DeligneDatum (K := K) π B) (u : Fin 2 → K) (hu : u ∈ stdLattice 𝒪 K)
    (h0 : (1 : B) ⊗ₜ[𝒪] (⟨u, hu⟩ : ↥(stdFullLattice (𝒪 := 𝒪) K).1) ∈ d.line (stdFullLattice K))
    (M : FullLattice 𝒪 K) (A : ℕ)
    (hl0 : algebraMap 𝒪 K (π ^ A) • (Pi.single 0 1 : Fin 2 → K) ∈ M.1)
    (hl1 : algebraMap 𝒪 K (π ^ A) • (Pi.single 1 1 : Fin 2 → K) ∈ M.1) :
    (1 : B) ⊗ₜ[𝒪] (⟨algebraMap 𝒪 K (π ^ A) • u, smul_mem_of_mem_stdLattice M _ hl0 hl1 u hu⟩ : ↥M.1) ∈ d.line M := by
  have hne : algebraMap 𝒪 K (π ^ A) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ (algebraMap_ne_zero' hπ)
  set c : Kˣ := Units.mk0 _ hne with hc
  have h1 : actBaseChange B (scalarGL c) (stdFullLattice K) ((1 : B) ⊗ₜ[𝒪] (⟨u, hu⟩ : ↥(stdFullLattice (𝒪 := 𝒪) K).1)) ∈
      d.line (FullLattice.act (scalarGL c) (stdFullLattice K)) := by
    rw [d.homothety c (stdFullLattice K)]
    exact Submodule.mem_map_of_mem h0
  rw [actBaseChange_tmul] at h1
  have hle : (FullLattice.act (scalarGL c) (stdFullLattice K)).1 ≤ M.1 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [mulVecLinR_apply, scalarGL_mulVec]
    exact smul_mem_of_mem_stdLattice M _ hl0 hl1 v hv
  have h2 := d.mono hle (Submodule.mem_map_of_mem (f := inclBaseChange B hle) h1)
  have key : inclBaseChange B hle ((1 : B) ⊗ₜ[𝒪] (latticeMapEquiv (scalarGL c) _ (⟨u, hu⟩ : ↥(stdFullLattice (𝒪 := 𝒪) K).1))) =
      (1 : B) ⊗ₜ[𝒪] (⟨algebraMap 𝒪 K (π ^ A) • u, smul_mem_of_mem_stdLattice M _ hl0 hl1 u hu⟩ : ↥M.1) := by
    show (1 : B) ⊗ₜ[𝒪] (Submodule.inclusion hle (latticeMapEquiv (scalarGL c) _ (⟨u, hu⟩ : ↥(stdFullLattice (𝒪 := 𝒪) K).1))) = _
    congr 1
    apply Subtype.ext
    show Matrix.mulVec ((scalarGL c : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) u =
      algebraMap 𝒪 K (π ^ A) • u
    rw [scalarGL_mulVec]; rfl
  rw [← key]
  exact h2

theorem not_forall_one_tmul_mem (hF : IsAdicFrame π ϖ R) (x : AdicPoint K π R) (u : Fin 2 → K)
    (hu : u ∈ stdLattice 𝒪 K) (i₀ : Fin 2) (hi : u i₀ = 1)
    (h : ∀ n, (1 : modPow π R n) ⊗ₜ[𝒪] (⟨u, hu⟩ : ↥(stdFullLattice (𝒪 := 𝒪) K).1) ∈ (x.pt n).line (stdFullLattice K)) :
    False := by
  have hπ := hF.irreducible
  haveI := isLocalRing_modPow hF 0
  set 𝔪₀ := IsLocalRing.maximalIdeal (modPow π R 0) with h𝔪₀
  obtain ⟨M', M, hle, hπM, h1, h2⟩ := (x.pt 0).nondeg 𝔪₀ (IsLocalRing.maximalIdeal.isMaximal _).isPrime
  obtain ⟨kup, hkup⟩ := exists_pow_isInteger_apply (K := K) hπ M
  obtain ⟨k0, hk0⟩ := exists_pow_smul_single_mem (K := K) hπ M' 0
  obtain ⟨k1, hk1⟩ := exists_pow_smul_single_mem (K := K) hπ M' 1
  set A := kup + k0 + k1 with hA
  have hl0' := pow_smul_single_mem_of_le M' 0 (show k0 ≤ A by omega) hk0
  have hl1' := pow_smul_single_mem_of_le M' 1 (show k1 ≤ A by omega) hk1
  have hl0 : algebraMap 𝒪 K (π ^ A) • (Pi.single 0 1 : Fin 2 → K) ∈ M.1 := hle hl0'
  have hl1 : algebraMap 𝒪 K (π ^ A) • (Pi.single 1 1 : Fin 2 → K) ∈ M.1 := hle hl1'
  have hup : ∀ v ∈ M.1, ∀ i, IsLocalization.IsInteger 𝒪 (algebraMap 𝒪 K (π ^ A) * v i) :=
    fun v hv i => isInteger_pow_mul_of_le (show kup ≤ A by omega) (hkup v hv i)
  have hlowM : algebraMap 𝒪 K (π ^ A) • u ∈ M.1 := smul_mem_of_mem_stdLattice M _ hl0 hl1 u hu
  have hlowM' : algebraMap 𝒪 K (π ^ A) • u ∈ M'.1 := smul_mem_of_mem_stdLattice M' _ hl0' hl1' u hu
  set n := 2 * A with hn
  have hE : (x.pt 0).EdgeNondegAt π 𝔪₀ M' M := ⟨hle, hπM, h1, h2⟩
  rw [← map_red_pt x n, edgeNondegAt_map_iff (red π n) (red_surjective π n)] at hE
  obtain ⟨_, _, h1n, h2n⟩ := hE
  set 𝔮 := Ideal.comap (red (R := R) π n) 𝔪₀ with h𝔮
  have hq : ∀ b, b ∉ 𝔮 → IsUnit b := by
    intro b hb
    apply isUnit_of_isUnit_red n b
    rw [h𝔮, Ideal.mem_comap, h𝔪₀, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hb
    exact hb
  set t₀ := primIdxU hπ M A u hlowM with ht₀
  set f := scaledU π A t₀ u with hf
  have hfM : f ∈ M.1 := scaledU_primIdxU_mem hπ M A u hlowM
  have hfA : (π ^ (2 * A - t₀)) • f = algebraMap 𝒪 K (π ^ A) • u :=
    pow_smul_scaledU hπ A t₀ (primIdxU_le hπ M A u hlowM) u
  have hj : 2 * A - t₀ ≤ n := Nat.sub_le _ _
  have hmemM := mem_sup_of_pow_smul_mem hF n (x.pt n) M ((1 : modPow π R n) ⊗ₜ[𝒪] (⟨f, hfM⟩ : ↥M.1)) _ hj
    (by rw [← one_tmul_eq_smul M f _ hfM hlowM _ hfA]; exact one_tmul_pow_smul_mem hπ (x.pt n) u hu (h n) M A hl0 hl1)
    𝔮 hq
  have hfM' : f ∈ M'.1 := by
    by_contra hf'
    exact h1n ⟨f, hfM⟩ hf' hmemM
  have hmemM' := mem_sup_of_pow_smul_mem hF n (x.pt n) M' ((1 : modPow π R n) ⊗ₜ[𝒪] (⟨f, hfM'⟩ : ↥M'.1)) _ hj
    (by rw [← one_tmul_eq_smul M' f _ hfM' hlowM' _ hfA]; exact one_tmul_pow_smul_mem hπ (x.pt n) u hu (h n) M' A hl0' hl1')
    𝔮 hq
  exact h2n ⟨f, hfM'⟩ (scaledU_primIdxU_not_div hπ M A u hlowM i₀ hi hup) hmemM'

theorem mem_line_of_coordEquiv_mem (x : AdicPoint K π R) (n : ℕ)
    (y : latticeBaseChange 𝒪 K (modPow π R n) (stdFullLattice K))
    (h : coordEquiv (𝒪 := 𝒪) K (modPow π R n) y ∈ lineCoord x n) : y ∈ (x.pt n).line (stdFullLattice K) := by
  rw [lineCoord, Submodule.mem_map] at h
  obtain ⟨y', hy', hyv⟩ := h
  rw [LinearEquiv.coe_coe] at hyv
  rwa [(coordEquiv (𝒪 := 𝒪) K (modPow π R n)).injective hyv] at hy'

theorem coordEquiv_one_tmul_vec {B : Type} [CommRing B] [Algebra 𝒪 B] (a b : 𝒪)
    (hu : (vec (algebraMap 𝒪 K a) (algebraMap 𝒪 K b) : Fin 2 → K) ∈ stdLattice 𝒪 K) :
    coordEquiv (𝒪 := 𝒪) K B ((1 : B) ⊗ₜ[𝒪] (⟨vec (algebraMap 𝒪 K a) (algebraMap 𝒪 K b), hu⟩ : ↥(stdFullLattice (𝒪 := 𝒪) K).1)) =
      vec (algebraMap 𝒪 B a) (algebraMap 𝒪 B b) := by
  have : (⟨vec (algebraMap 𝒪 K a) (algebraMap 𝒪 K b), hu⟩ : ↥(stdFullLattice (𝒪 := 𝒪) K).1) =
      a • stdBasisVec (𝒪 := 𝒪) K 0 + b • stdBasisVec (𝒪 := 𝒪) K 1 := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul, vec, algebraMap_smul]
    rfl
  rw [this, tmul_add, tmul_smul, tmul_smul, ← algebraMap_smul B a, ← algebraMap_smul B b, map_add, map_smul, map_smul,
    coordEquiv_tmul, coordEquiv_tmul]
  rfl

theorem vec_mem_stdLattice (a b : 𝒪) : (vec (algebraMap 𝒪 K a) (algebraMap 𝒪 K b) : Fin 2 → K) ∈ stdLattice 𝒪 K := by
  rw [mem_stdLattice]
  intro i
  fin_cases i
  · exact ⟨a, by simp⟩
  · exact ⟨b, by simp⟩

end KeyU
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane.CerednikDrinfeld.FormalOmega.T2aAux"

end CerednikDrinfeld.FormalOmega.T2aAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane.CerednikDrinfeld.FormalOmega.T2aAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane.CerednikDrinfeld.FormalOmega.T2aAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane.CerednikDrinfeld.FormalOmega.T2aAux"

open CerednikDrinfeld.FormalOmega.T2aAux in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪}
    {C : Type} [Field C] [Algebra K C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]
    (ϖ : PseudoUniformizer K C) (hF : IsAdicFrame π ϖ R) (x : AdicPoint K π R) :
    x.toOmega C ∈ Omega.upperHalfPlane K C := by
  classical
  rw [mem_upperHalfPlane_iff]
  intro a ha
  have hπ := hF.irreducible
  by_cases h0 : ∃ c, lineCoord x 0 = Submodule.span _ {vec c 1}
  ·
    choose c hc using typeII_all hF x h0
    have hcompat : ∀ n, modPowTransition π R n (c (n + 1)) = c n := by
      intro n
      have h' := lineCoord_eq_of_succ x n (c (n + 1)) 1 (hc (n + 1))
      rw [map_one, hc n] at h'
      exact (eq_of_span_vec_one_eq' h').symm
    obtain ⟨L, hL⟩ := exists_lift hF c hcompat
    have hstd : x.stdLine = Submodule.span R {vec L 1} :=
      stdLine_eq_span_II hF x L (fun n => by rw [hc n, hL n])
    have hlineC : x.lineC C = Submodule.span C {vec (algebraMap R C L) 1} := by
      rw [lineC_eq_of_stdLine_eq x _ hstd, algebraMap_vec, map_one]
    have hmemL : (![algebraMap R C L, 1] : Fin 2 → C) ∈ x.lineC C := by
      rw [hlineC, vecLit_eq_vec, mem_span_vec_one_iff']; simp
    have huniq : ∃! z : C, (![z, 1] : Fin 2 → C) ∈ x.lineC C := by
      refine ⟨algebraMap R C L, hmemL, fun z hz => ?_⟩
      rw [hlineC, vecLit_eq_vec, mem_span_vec_one_iff'] at hz
      simpa using hz
    have hz : x.toOmega C = algebraMap R C L := huniq.unique (AdicPoint.vecCons_toOmega_mem C x huniq) hmemL
    rw [hz] at ha
    obtain ⟨a₀, ha₀⟩ := (hF.integers a).mp (by rw [ha]; exact hF.v_algebraMap_le_one L)
    have hL' : algebraMap 𝒪 R a₀ = L := hF.injective (by
      rw [← IsScalarTower.algebraMap_apply 𝒪 R C, IsScalarTower.algebraMap_apply 𝒪 K C, ha₀, ha])
    apply not_forall_one_tmul_mem hF x (vec (algebraMap 𝒪 K a₀) (algebraMap 𝒪 K 1)) (vec_mem_stdLattice a₀ 1) 1
      (by rw [vec_apply_one, map_one])
    intro n
    apply mem_line_of_coordEquiv_mem x n
    rw [coordEquiv_one_tmul_vec, hc n, ← hL n, ← hL', map_one, mem_span_vec_one_iff', vec_apply_zero, vec_apply_one,
      mul_one, IsScalarTower.algebraMap_apply 𝒪 R (modPow π R n), Ideal.Quotient.algebraMap_eq]
  ·
    choose c hc using typeI_all hF x h0
    have hcompat : ∀ n, modPowTransition π R n (c (n + 1)) = c n := by
      intro n
      have h' := lineCoord_eq_of_succ x n 1 (c (n + 1)) (hc (n + 1))
      rw [map_one, hc n] at h'
      exact (eq_of_span_vec_one_eq h').symm
    obtain ⟨L, hL⟩ := exists_lift hF c hcompat
    have hstd : x.stdLine = Submodule.span R {vec 1 L} :=
      stdLine_eq_span_I hF x L (fun n => by rw [hc n, hL n])
    have hL0 : L ≠ 0 := by
      intro hL0
      apply not_forall_one_tmul_single_mem hF x
      intro n
      apply one_tmul_single_mem_of_lineCoord x n
      rw [hc n, ← hL n, hL0, map_zero]
    have hLC : algebraMap R C L ≠ 0 := fun h => hL0 (hF.injective (by rw [h, map_zero]))
    have hlineC : x.lineC C = Submodule.span C {vec 1 (algebraMap R C L)} := by
      rw [lineC_eq_of_stdLine_eq x _ hstd, algebraMap_vec, map_one]
    have hmemL : (![(algebraMap R C L)⁻¹, 1] : Fin 2 → C) ∈ x.lineC C := by
      rw [hlineC, vecLit_eq_vec, mem_span_vec_one_iff]; simp [mul_inv_cancel₀ hLC]
    have huniq : ∃! z : C, (![z, 1] : Fin 2 → C) ∈ x.lineC C := by
      refine ⟨(algebraMap R C L)⁻¹, hmemL, fun z hz => ?_⟩
      rw [hlineC, vecLit_eq_vec, mem_span_vec_one_iff] at hz
      simp only [vec_apply_one, vec_apply_zero] at hz
      calc z = (algebraMap R C L)⁻¹ * (algebraMap R C L * z) := by rw [← mul_assoc, inv_mul_cancel₀ hLC, one_mul]
        _ = (algebraMap R C L)⁻¹ := by rw [← hz, mul_one]
    have hz : x.toOmega C = (algebraMap R C L)⁻¹ := huniq.unique (AdicPoint.vecCons_toOmega_mem C x huniq) hmemL
    rw [hz] at ha

    have ha0 : a ≠ 0 := by
      intro h; rw [h, map_zero] at ha; exact inv_ne_zero hLC ha.symm
    have hainv : algebraMap K C a⁻¹ = algebraMap R C L := by rw [map_inv₀, ha, inv_inv]
    obtain ⟨b₀, hb₀⟩ := (hF.integers a⁻¹).mp (by rw [hainv]; exact hF.v_algebraMap_le_one L)
    have hL' : algebraMap 𝒪 R b₀ = L := hF.injective (by
      rw [← IsScalarTower.algebraMap_apply 𝒪 R C, IsScalarTower.algebraMap_apply 𝒪 K C, hb₀, hainv])
    apply not_forall_one_tmul_mem hF x (vec (algebraMap 𝒪 K 1) (algebraMap 𝒪 K b₀)) (vec_mem_stdLattice 1 b₀) 0
      (by rw [vec_apply_zero, map_one])
    intro n
    apply mem_line_of_coordEquiv_mem x n
    rw [coordEquiv_one_tmul_vec, hc n, ← hL n, ← hL', map_one, mem_span_vec_one_iff, vec_apply_zero, vec_apply_one,
      mul_one, IsScalarTower.algebraMap_apply 𝒪 R (modPow π R n), Ideal.Quotient.algebraMap_eq]

end S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane (solution)
