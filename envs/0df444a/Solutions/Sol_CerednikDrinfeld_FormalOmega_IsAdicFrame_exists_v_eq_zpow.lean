-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.IsAdicFrame.exists_v_eq_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/6ee42de0-707a-5925-8002-7c6a9a29c697

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
p2m_open "LT.LatticeTree CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.moebius Omega.pmoebius Omega.pmoebius_mk"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt DeligneDatum.InEdgeChart modPow span_pow_succ_le modPowTransition AdicPoint stdFullLattice stdBasisVec coordToTensor AdicPoint.mem_stdLine_iff AdicPoint.act_pt AdicPoint.lineC AdicPoint.vecCons_toOmega_mem coe_ofEq_apply coe_latticeMapEquiv_apply actBaseChange_tmul rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum lineBaseChange"
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
p2m_export "CerednikDrinfeld" "Omega.moebius Omega.pmoebius Omega.pmoebius_mk"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt DeligneDatum.InEdgeChart modPow span_pow_succ_le modPowTransition AdicPoint stdFullLattice stdBasisVec coordToTensor AdicPoint.mem_stdLine_iff AdicPoint.act_pt AdicPoint.lineC AdicPoint.vecCons_toOmega_mem coe_ofEq_apply coe_latticeMapEquiv_apply actBaseChange_tmul rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum lineBaseChange"
namespace T3Aux
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

end CerednikDrinfeld.FormalOmega.T3Aux
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.moebius Omega.pmoebius Omega.pmoebius_mk"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt DeligneDatum.InEdgeChart modPow span_pow_succ_le modPowTransition AdicPoint stdFullLattice stdBasisVec coordToTensor AdicPoint.mem_stdLine_iff AdicPoint.act_pt AdicPoint.lineC AdicPoint.vecCons_toOmega_mem coe_ofEq_apply coe_latticeMapEquiv_apply actBaseChange_tmul rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum lineBaseChange"
namespace T3Aux
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
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"

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
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"

end CerednikDrinfeld.FormalOmega.T3Aux
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.moebius Omega.pmoebius Omega.pmoebius_mk"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt DeligneDatum.InEdgeChart modPow span_pow_succ_le modPowTransition AdicPoint stdFullLattice stdBasisVec coordToTensor AdicPoint.mem_stdLine_iff AdicPoint.act_pt AdicPoint.lineC AdicPoint.vecCons_toOmega_mem coe_ofEq_apply coe_latticeMapEquiv_apply actBaseChange_tmul rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum lineBaseChange"
namespace T3Aux
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

open TensorProduct CerednikDrinfeld.FormalOmega.LevelAux

section ActCoord

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}
variable {R : Type} [CommRing R] [Algebra 𝒪 R]

theorem mem_lineCoord_act_iff (x : AdicPoint K π R) (g : GL (Fin 2) K) (n : ℕ) (w : Fin 2 → modPow π R n) :
    w ∈ lineCoord (x.act g) n ↔
      actBaseChange (modPow π R n) g⁻¹ (stdFullLattice K) ((coordEquiv (𝒪 := 𝒪) K (modPow π R n)).symm w) ∈
        (x.pt n).line (FullLattice.act g⁻¹ (stdFullLattice K)) := by
  rw [lineCoord, AdicPoint.act_pt]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact hy
  · intro h
    refine ⟨(coordEquiv (𝒪 := 𝒪) K (modPow π R n)).symm w, h, ?_⟩
    rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

theorem exists_pow_isInteger_entries (hπ : Irreducible π) (g : GL (Fin 2) K) :
    ∃ A : ℕ, ∀ i j, IsLocalization.IsInteger 𝒪 (algebraMap 𝒪 K (π ^ A) * (g : Matrix (Fin 2) (Fin 2) K) i j) := by
  classical
  obtain ⟨A, hA⟩ := exists_pow_isInteger (K := K) hπ
    (Finset.univ.biUnion fun i : Fin 2 => Finset.univ.image fun j : Fin 2 => (g : Matrix (Fin 2) (Fin 2) K) i j)
  refine ⟨A, fun i j => hA _ ?_⟩
  rw [Finset.mem_biUnion]
  exact ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

variable (g : GL (Fin 2) K) (A : ℕ)
  (hA : ∀ i j, IsLocalization.IsInteger 𝒪 (algebraMap 𝒪 K (π ^ A) * (g : Matrix (Fin 2) (Fin 2) K) i j))

include hA

noncomputable def intMat : Matrix (Fin 2) (Fin 2) 𝒪 := fun i j => Classical.choose (hA i j)

theorem algebraMap_intMat (i j : Fin 2) :
    algebraMap 𝒪 K (intMat g A hA i j) = algebraMap 𝒪 K (π ^ A) * (g : Matrix (Fin 2) (Fin 2) K) i j :=
  Classical.choose_spec (hA i j)

theorem col_eq (i : Fin 2) :
    algebraMap 𝒪 K (intMat g A hA 0 i) • (Pi.single 0 1 : Fin 2 → K) +
        algebraMap 𝒪 K (intMat g A hA 1 i) • (Pi.single 1 1 : Fin 2 → K) =
      algebraMap 𝒪 K (π ^ A) • Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) K) (Pi.single i 1) := by
  rw [Matrix.mulVec_single_one]
  funext k
  fin_cases k <;> simp [Pi.single_apply, algebraMap_intMat]

theorem pow_smul_single_eq (i : Fin 2) :
    algebraMap 𝒪 K (π ^ A) • (Pi.single i 1 : Fin 2 → K) =
      (intMat g A hA 0 i) • Matrix.mulVec ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) (Pi.single 0 1) +
      (intMat g A hA 1 i) • Matrix.mulVec ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) (Pi.single 1 1) := by
  rw [← algebraMap_smul K (intMat g A hA 0 i), ← algebraMap_smul K (intMat g A hA 1 i), ← Matrix.mulVec_smul,
    ← Matrix.mulVec_smul, ← Matrix.mulVec_add, col_eq, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  have : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [this, Matrix.one_mulVec]

theorem pow_smul_single_mem_act (i : Fin 2) :
    algebraMap 𝒪 K (π ^ A) • (Pi.single i 1 : Fin 2 → K) ∈ (FullLattice.act g⁻¹ (stdFullLattice (𝒪 := 𝒪) K)).1 := by
  have hmem : algebraMap 𝒪 K (π ^ A) • Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) K) (Pi.single i 1) ∈ stdLattice 𝒪 K := by
    rw [← col_eq g A hA, algebraMap_smul, algebraMap_smul]
    exact add_mem (Submodule.smul_mem _ _ (single_one_mem_stdLattice 𝒪 K 0))
      (Submodule.smul_mem _ _ (single_one_mem_stdLattice 𝒪 K 1))
  have := mulVec_mem_latticeMap (g := g⁻¹) hmem
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec] at this
  have h1 : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rwa [h1, Matrix.one_mulVec] at this

theorem mk_pow_smul_single_eq (i : Fin 2) :
    (⟨algebraMap 𝒪 K (π ^ A) • (Pi.single i 1 : Fin 2 → K), pow_smul_single_mem_act g A hA i⟩ :
        ↥(FullLattice.act g⁻¹ (stdFullLattice (𝒪 := 𝒪) K)).1) =
      (intMat g A hA 0 i) • latticeMapEquiv g⁻¹ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 0) +
      (intMat g A hA 1 i) • latticeMapEquiv g⁻¹ (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 1) := by
  apply Subtype.ext
  rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, coe_latticeMapEquiv_apply, coe_latticeMapEquiv_apply]
  exact pow_smul_single_eq g A hA i

variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem push_mem (hπ : Irreducible π) (d : DeligneDatum (K := K) π B) (v : Fin 2 → B)
    (hv : (coordEquiv (𝒪 := 𝒪) K B).symm v ∈ d.line (stdFullLattice K)) :
    v 0 ⊗ₜ[𝒪] (⟨_, pow_smul_single_mem_act g A hA 0⟩ : ↥(FullLattice.act g⁻¹ (stdFullLattice (𝒪 := 𝒪) K)).1) +
      v 1 ⊗ₜ[𝒪] (⟨_, pow_smul_single_mem_act g A hA 1⟩ : ↥(FullLattice.act g⁻¹ (stdFullLattice (𝒪 := 𝒪) K)).1) ∈
      d.line (FullLattice.act g⁻¹ (stdFullLattice K)) := by
  have hne : algebraMap 𝒪 K (π ^ A) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ (algebraMap_ne_zero' hπ)
  set c : Kˣ := Units.mk0 _ hne with hc
  have h1 : actBaseChange B (scalarGL c) (stdFullLattice K) ((coordEquiv (𝒪 := 𝒪) K B).symm v) ∈
      d.line (FullLattice.act (scalarGL c) (stdFullLattice K)) := by
    rw [d.homothety c (stdFullLattice K)]
    exact Submodule.mem_map_of_mem hv
  have hle : (FullLattice.act (scalarGL c) (stdFullLattice K)).1 ≤ (FullLattice.act g⁻¹ (stdFullLattice (𝒪 := 𝒪) K)).1 := by
    rintro _ ⟨w, hw, rfl⟩
    rw [mulVecLinR_apply, scalarGL_mulVec]
    exact smul_mem_of_mem_stdLattice _ _ (pow_smul_single_mem_act g A hA 0) (pow_smul_single_mem_act g A hA 1) w hw
  have h2 := d.mono hle (Submodule.mem_map_of_mem (f := inclBaseChange B hle) h1)
  rw [coordEquiv_symm_apply, Fin.sum_univ_two, map_add, map_add, actBaseChange_tmul, actBaseChange_tmul] at h2
  have key : ∀ (i : Fin 2), inclBaseChange B hle (v i ⊗ₜ[𝒪] latticeMapEquiv (scalarGL c) _ (stdBasisVec (𝒪 := 𝒪) K i)) =
      v i ⊗ₜ[𝒪] (⟨_, pow_smul_single_mem_act g A hA i⟩ : ↥(FullLattice.act g⁻¹ (stdFullLattice (𝒪 := 𝒪) K)).1) := by
    intro i
    show v i ⊗ₜ[𝒪] (Submodule.inclusion hle (latticeMapEquiv (scalarGL c) _ (stdBasisVec (𝒪 := 𝒪) K i))) = _
    congr 1
    apply Subtype.ext
    show Matrix.mulVec ((scalarGL c : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) (Pi.single i 1) =
      algebraMap 𝒪 K (π ^ A) • (Pi.single i 1 : Fin 2 → K)
    rw [scalarGL_mulVec]; rfl
  rw [← key 0, ← key 1]
  exact h2

theorem mulVec_mem_lineCoord_act (hπ : Irreducible π) (x : AdicPoint K π R) (n : ℕ) (v : Fin 2 → modPow π R n)
    (hv : v ∈ lineCoord x n) :
    Matrix.mulVec ((intMat g A hA).map (algebraMap 𝒪 (modPow π R n))) v ∈ lineCoord (x.act g) n := by
  rw [mem_lineCoord_act_iff, coordEquiv_symm_apply, Fin.sum_univ_two, map_add, actBaseChange_tmul, actBaseChange_tmul]
  have hv' : (coordEquiv (𝒪 := 𝒪) K (modPow π R n)).symm v ∈ (x.pt n).line (stdFullLattice K) := by
    rw [lineCoord, Submodule.mem_map_equiv] at hv; exact hv
  have h := push_mem g A hA hπ (x.pt n) v hv'
  erw [mk_pow_smul_single_eq g A hA 0, mk_pow_smul_single_eq g A hA 1, tmul_add, tmul_add, tmul_smul, tmul_smul,
    tmul_smul, tmul_smul, ← algebraMap_smul (modPow π R n) (intMat g A hA 0 0),
    ← algebraMap_smul (modPow π R n) (intMat g A hA 1 0), ← algebraMap_smul (modPow π R n) (intMat g A hA 0 1),
    ← algebraMap_smul (modPow π R n) (intMat g A hA 1 1), smul_tmul', smul_tmul', smul_tmul', smul_tmul'] at h
  have e0 : (Matrix.mulVec ((intMat g A hA).map (algebraMap 𝒪 (modPow π R n))) v) 0 =
      algebraMap 𝒪 (modPow π R n) (intMat g A hA 0 0) • v 0 + algebraMap 𝒪 (modPow π R n) (intMat g A hA 0 1) • v 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply]
  have e1 : (Matrix.mulVec ((intMat g A hA).map (algebraMap 𝒪 (modPow π R n))) v) 1 =
      algebraMap 𝒪 (modPow π R n) (intMat g A hA 1 0) • v 0 + algebraMap 𝒪 (modPow π R n) (intMat g A hA 1 1) • v 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply]
  rw [e0, e1, add_tmul, add_tmul]
  erw [add_add_add_comm] at h
  exact h

end ActCoord
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"

end CerednikDrinfeld.FormalOmega.T3Aux
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.moebius Omega.pmoebius Omega.pmoebius_mk"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt DeligneDatum.InEdgeChart modPow span_pow_succ_le modPowTransition AdicPoint stdFullLattice stdBasisVec coordToTensor AdicPoint.mem_stdLine_iff AdicPoint.act_pt AdicPoint.lineC AdicPoint.vecCons_toOmega_mem coe_ofEq_apply coe_latticeMapEquiv_apply actBaseChange_tmul rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum lineBaseChange"
namespace T3Aux
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

open TensorProduct CerednikDrinfeld.FormalOmega.LevelAux

section LimitVec

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}
  {C : Type} [Field C] [Algebra K C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]
  {ϖ : PseudoUniformizer K C}

theorem map_vec {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) (a b : S) :
    (fun i => f (vec a b i)) = vec (f a) (f b) := by
  funext j; fin_cases j <;> simp

theorem exists_limitVec (hF : IsAdicFrame π ϖ R) (x : AdicPoint K π R) :
    ∃ (v : Fin 2 → R) (i₀ : Fin 2) (μ : C), v i₀ = 1 ∧ μ ≠ 0 ∧
      (∀ n, lineCoord x n = Submodule.span _ {fun i => Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) (v i)}) ∧
      (fun i => algebraMap R C (v i)) = μ • vec (x.toOmega C) 1 := by
  classical
  by_cases h0 : ∃ c, lineCoord x 0 = Submodule.span _ {vec c 1}
  · choose c hc using typeII_all hF x h0
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
    refine ⟨vec L 1, 1, 1, vec_apply_one _ _, one_ne_zero, fun n => ?_, ?_⟩
    · rw [hc n, ← hL n, map_vec, map_one]
    · rw [hz, one_smul, map_vec (algebraMap R C), map_one]
  · choose c hc using typeI_all hF x h0
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
    refine ⟨vec 1 L, 0, algebraMap R C L, vec_apply_zero _ _, hLC, fun n => ?_, ?_⟩
    · rw [hc n, ← hL n, map_vec, map_one]
    · rw [hz, smul_vec, mul_inv_cancel₀ hLC, mul_one, map_vec (algebraMap R C), map_one]

theorem eq_smul_of_forall_mem (hF : IsAdicFrame π ϖ R) (u v' : Fin 2 → R) (i₀ : Fin 2) (hi : v' i₀ = 1)
    (h : ∀ n, (fun i => Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) (u i)) ∈
      Submodule.span (modPow π R n) {fun i => Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) (v' i)}) :
    u = (u i₀) • v' := by
  funext j
  rw [Pi.smul_apply, smul_eq_mul, ← sub_eq_zero]
  apply eq_zero_of_forall_mem hF
  intro n
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (h n)
  have hr0 := congrFun hr i₀
  have hrj := congrFun hr j
  simp only [Pi.smul_apply, smul_eq_mul, hi, map_one, mul_one] at hr0 hrj
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← hrj, ← hr0, sub_self]

theorem mulVec_map_mk (α : Matrix (Fin 2) (Fin 2) 𝒪) (v : Fin 2 → R) (n : ℕ) :
    Matrix.mulVec (α.map (algebraMap 𝒪 (modPow π R n)))
        (fun i => Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) (v i)) =
      fun j => Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) (Matrix.mulVec (α.map (algebraMap 𝒪 R)) v j) := by
  funext j
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply, map_add, map_mul]
  rw [IsScalarTower.algebraMap_apply 𝒪 R (modPow π R n) (α j 0), IsScalarTower.algebraMap_apply 𝒪 R (modPow π R n) (α j 1),
    Ideal.Quotient.algebraMap_eq]

end LimitVec
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"

end CerednikDrinfeld.FormalOmega.T3Aux
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"

namespace CerednikDrinfeld p2m_export "CerednikDrinfeld" "Omega.moebius Omega.pmoebius Omega.pmoebius_mk" namespace FormalOmega p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt DeligneDatum.InEdgeChart modPow span_pow_succ_le modPowTransition AdicPoint stdFullLattice stdBasisVec coordToTensor AdicPoint.mem_stdLine_iff AdicPoint.act_pt AdicPoint.lineC AdicPoint.vecCons_toOmega_mem coe_ofEq_apply coe_latticeMapEquiv_apply actBaseChange_tmul rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum lineBaseChange" namespace T3Aux end CerednikDrinfeld.FormalOmega.T3Aux
p2m_open_scoped "CerednikDrinfeld CerednikDrinfeld.FormalOmega" in
open CerednikDrinfeld.FormalOmega.T3Aux in
theorem CerednikDrinfeld.FormalOmega.T3Aux.toOmega_act'
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪}
    {C : Type} [Field C] [Algebra K C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]
    (ϖ : PseudoUniformizer K C) (hF : IsAdicFrame π ϖ R) (g : GL (Fin 2) K) (x : AdicPoint K π R) :
    (x.act g).toOmega C = Omega.pmoebius K (Matrix.ProjGenLinGroup.mk g) (x.toOmega C) := by
  classical
  have hπ := hF.irreducible
  obtain ⟨A, hA⟩ := exists_pow_isInteger_entries (K := K) hπ g
  obtain ⟨v, i₀, μ, hvi, hμ, hline, hvC⟩ := exists_limitVec hF x
  obtain ⟨v', i₀', μ', hvi', hμ', hline', hvC'⟩ := exists_limitVec hF (x.act g)
  set z := x.toOmega C with hz
  set z' := (x.act g).toOmega C with hz'
  set α := intMat g A hA with hα
  set u : Fin 2 → R := Matrix.mulVec (α.map (algebraMap 𝒪 R)) v with hu

  have hmem : ∀ n, (fun i => Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) (u i)) ∈
      Submodule.span (modPow π R n) {fun i => Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) (v' i)} := by
    intro n
    rw [← hline' n, hu, ← mulVec_map_mk]
    apply mulVec_mem_lineCoord_act g A hA hπ x n
    rw [hline n]
    exact Submodule.mem_span_singleton_self _
  have hlam := eq_smul_of_forall_mem hF u v' i₀' hvi' hmem

  set P : C := algebraMap K C (algebraMap 𝒪 K (π ^ A)) * μ with hP
  have hPne : P ≠ 0 := by
    refine mul_ne_zero ?_ hμ
    rw [map_ne_zero, map_pow]
    exact pow_ne_zero _ (algebraMap_ne_zero' hπ)
  have hvCi : ∀ i, algebraMap R C (v i) = μ * vec z 1 i := fun i => by
    have := congrFun hvC i; simpa only [Pi.smul_apply, smul_eq_mul] using this
  have hvCi' : ∀ i, algebraMap R C (v' i) = μ' * vec z' 1 i := fun i => by
    have := congrFun hvC' i; simpa only [Pi.smul_apply, smul_eq_mul] using this
  have hαC : ∀ i j, algebraMap R C (algebraMap 𝒪 R (α i j)) =
      algebraMap K C (algebraMap 𝒪 K (π ^ A)) * algebraMap K C ((g : Matrix (Fin 2) (Fin 2) K) i j) := by
    intro i j
    rw [← IsScalarTower.algebraMap_apply 𝒪 R C, IsScalarTower.algebraMap_apply 𝒪 K C, hα, algebraMap_intMat, map_mul]

  have hcoord : ∀ j, P * (algebraMap K C ((g : Matrix (Fin 2) (Fin 2) K) j 0) * z +
      algebraMap K C ((g : Matrix (Fin 2) (Fin 2) K) j 1)) = algebraMap R C (u i₀') * (μ' * vec z' 1 j) := by
    intro j
    have h1 := congrArg (algebraMap R C) (congrFun hlam j)
    rw [Pi.smul_apply, smul_eq_mul, map_mul, hvCi' j] at h1
    rw [← h1, hu]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply, map_add, map_mul, hαC, hvCi,
      vec_apply_zero, vec_apply_one, hP]
    ring
  have hq0 := hcoord 1
  have hp0 := hcoord 0
  simp only [vec_apply_one, vec_apply_zero, mul_one] at hq0 hp0
  set p := algebraMap K C ((g : Matrix (Fin 2) (Fin 2) K) 0 0) * z + algebraMap K C ((g : Matrix (Fin 2) (Fin 2) K) 0 1)
    with hp
  set q := algebraMap K C ((g : Matrix (Fin 2) (Fin 2) K) 1 0) * z + algebraMap K C ((g : Matrix (Fin 2) (Fin 2) K) 1 1)
    with hq

  have hqne : q ≠ 0 := by
    intro hq0'
    have hl : algebraMap R C (u i₀') * μ' = 0 := by rw [← hq0, hq0', mul_zero]
    have hp0' : p = 0 := by
      have : P * p = 0 := by rw [hp0, ← mul_assoc, hl, zero_mul]
      exact (mul_eq_zero.mp this).resolve_left hPne

    set gC : Matrix (Fin 2) (Fin 2) C := (g : Matrix (Fin 2) (Fin 2) K).map (algebraMap K C) with hgC
    set giC : Matrix (Fin 2) (Fin 2) C := ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map (algebraMap K C) with hgiC
    have hmv : Matrix.mulVec gC (vec z 1) = 0 := by
      funext j
      fin_cases j
      · show Matrix.mulVec gC (vec z 1) 0 = 0
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hgC, Matrix.map_apply, vec_apply_zero, vec_apply_one,
          mul_one]
        exact hp0'
      · show Matrix.mulVec gC (vec z 1) 1 = 0
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hgC, Matrix.map_apply, vec_apply_zero, vec_apply_one,
          mul_one]
        exact hq0'
    have hinv : giC * gC = 1 := by
      rw [hgiC, hgC, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have : (vec z 1 : Fin 2 → C) = 0 := by
      rw [← Matrix.one_mulVec (vec z 1), ← hinv, ← Matrix.mulVec_mulVec, hmv, Matrix.mulVec_zero]
    have := congrFun this 1
    simp at this

  have hz'eq : z' = p / q := by
    rw [eq_div_iff hqne]
    have h2 : P * (z' * q) = P * p := by
      rw [hp0, mul_left_comm P z' q, hq0]; ring
    exact mul_left_cancel₀ hPne h2
  rw [Omega.pmoebius_mk K g z hqne, Omega.moebius]
  exact hz'eq

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.moebius Omega.pmoebius Omega.pmoebius_mk"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt DeligneDatum.InEdgeChart modPow span_pow_succ_le modPowTransition AdicPoint stdFullLattice stdBasisVec coordToTensor AdicPoint.mem_stdLine_iff AdicPoint.act_pt AdicPoint.lineC AdicPoint.vecCons_toOmega_mem coe_ofEq_apply coe_latticeMapEquiv_apply actBaseChange_tmul rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum lineBaseChange"
namespace T3Aux
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

section LatticeBasis

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}

theorem isTorsionFree_lattice (M : FullLattice 𝒪 K) : Module.IsTorsionFree 𝒪 ↥M.1 := by
  haveI : FaithfulSMul 𝒪 K := (faithfulSMul_iff_algebraMap_injective 𝒪 K).mpr (IsFractionRing.injective 𝒪 K)
  refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
  by_cases hr : r = 0
  · exact Or.inl hr
  · right
    apply Subtype.ext
    have : r • (m : Fin 2 → K) = 0 := by rw [← Submodule.coe_smul, h, Submodule.coe_zero]
    rw [← algebraMap_smul K r, smul_eq_zero] at this
    exact this.resolve_left ((map_ne_zero_iff _ (IsFractionRing.injective 𝒪 K)).mpr hr)

theorem finite_lattice (M : FullLattice 𝒪 K) : Module.Finite 𝒪 ↥M.1 :=
  Module.Finite.iff_fg.mpr M.2.1

theorem linearIndependent_coe (hπ : Irreducible π) (M : FullLattice 𝒪 K) {n : ℕ} (b : Module.Basis (Fin n) 𝒪 ↥M.1) :
    LinearIndependent K (fun j => ((b j : ↥M.1) : Fin 2 → K)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  obtain ⟨k, hk⟩ := exists_pow_isInteger (K := K) hπ (Finset.univ.image c)
  choose r hr using fun i => hk (c i) (Finset.mem_image_of_mem c (Finset.mem_univ i))
  have hsum : ∑ i, r i • b i = 0 := by
    apply Subtype.ext
    rw [Submodule.coe_sum, Submodule.coe_zero]
    have : ∑ i, ((r i • b i : ↥M.1) : Fin 2 → K) = algebraMap 𝒪 K (π ^ k) • ∑ i, c i • ((b i : ↥M.1) : Fin 2 → K) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Submodule.coe_smul, smul_smul, ← hr i, algebraMap_smul]
    rw [this, hc, smul_zero]
  have hri : r j = 0 := Fintype.linearIndependent_iff.mp b.linearIndependent r hsum j
  have : algebraMap 𝒪 K (π ^ k) * c j = 0 := by rw [← hr j, hri, map_zero]
  rcases mul_eq_zero.mp this with h | h
  · rw [map_pow] at h; exact absurd h (pow_ne_zero _ (algebraMap_ne_zero' hπ))
  · exact h

theorem span_range_coe (M : FullLattice 𝒪 K) {n : ℕ} (b : Module.Basis (Fin n) 𝒪 ↥M.1) :
    Submodule.span K (Set.range fun j => ((b j : ↥M.1) : Fin 2 → K)) = ⊤ := by
  apply le_antisymm le_top
  rw [← M.2.2, Submodule.span_le]
  intro m hm
  have : (⟨m, hm⟩ : ↥M.1) = ∑ j, b.repr ⟨m, hm⟩ j • b j := (b.sum_repr ⟨m, hm⟩).symm
  have hm' : m = ∑ j, algebraMap 𝒪 K (b.repr ⟨m, hm⟩ j) • ((b j : ↥M.1) : Fin 2 → K) := by
    have := congrArg Subtype.val this
    rw [Submodule.coe_sum] at this
    exact this.trans (Finset.sum_congr rfl fun j _ => by rw [Submodule.coe_smul, algebraMap_smul])
  rw [hm']
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem exists_basis (hπ : Irreducible π) (M : FullLattice 𝒪 K) : Nonempty (Module.Basis (Fin 2) 𝒪 ↥M.1) := by
  haveI := isTorsionFree_lattice M
  haveI := finite_lattice M
  obtain ⟨n, b⟩ := (Module.basisOfFiniteTypeTorsionFree' : Σ n : ℕ, Module.Basis (Fin n) 𝒪 ↥M.1)
  have bK : Module.Basis (Fin n) K (Fin 2 → K) :=
    Module.Basis.mk (linearIndependent_coe hπ M b) (span_range_coe M b).ge
  have hn : n = 2 := by
    have := Module.finrank_eq_card_basis bK
    rw [Module.finrank_fin_fun, Fintype.card_fin] at this
    exact this.symm
  subst hn
  exact ⟨b⟩

theorem exists_act_eq (hπ : Irreducible π) (M : FullLattice 𝒪 K) :
    ∃ g : GL (Fin 2) K, FullLattice.act g (stdFullLattice K) = M := by
  classical
  obtain ⟨b⟩ := exists_basis hπ M
  set A : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j => ((b j : ↥M.1) : Fin 2 → K) i with hAdef
  have hcol : A.col = fun j => ((b j : ↥M.1) : Fin 2 → K) := by
    funext j i; rfl
  have hunit : IsUnit A := Matrix.linearIndependent_cols_iff_isUnit.mp (by rw [hcol]; exact linearIndependent_coe hπ M b)
  refine ⟨hunit.unit, ?_⟩
  have hmulVec : ∀ w : Fin 2 → K, Matrix.mulVec A w = w 0 • ((b 0 : ↥M.1) : Fin 2 → K) + w 1 • ((b 1 : ↥M.1) : Fin 2 → K) := by
    intro w; funext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hAdef, Matrix.of_apply, mul_comm]
  apply Subtype.ext
  show latticeMap hunit.unit (stdLattice 𝒪 K) = M.1
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    rw [mulVecLinR_apply, IsUnit.unit_spec, hmulVec]
    rw [SetLike.mem_coe, mem_stdLattice] at hw
    obtain ⟨r0, hr0⟩ := hw 0
    obtain ⟨r1, hr1⟩ := hw 1
    rw [← hr0, ← hr1, algebraMap_smul, algebraMap_smul]
    exact add_mem (Submodule.smul_mem _ _ (b 0).2) (Submodule.smul_mem _ _ (b 1).2)
  · intro m hm
    refine ⟨fun j => algebraMap 𝒪 K (b.repr ⟨m, hm⟩ j), ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_stdLattice]; intro j; exact ⟨_, rfl⟩
    · rw [mulVecLinR_apply, IsUnit.unit_spec, hmulVec, algebraMap_smul, algebraMap_smul]
      have := congrArg Subtype.val (b.sum_repr ⟨m, hm⟩)
      rw [Submodule.coe_sum, Fin.sum_univ_two, Submodule.coe_smul, Submodule.coe_smul] at this
      exact this

end LatticeBasis
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"

end CerednikDrinfeld.FormalOmega.T3Aux
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.moebius Omega.pmoebius Omega.pmoebius_mk"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt DeligneDatum.InEdgeChart modPow span_pow_succ_le modPowTransition AdicPoint stdFullLattice stdBasisVec coordToTensor AdicPoint.mem_stdLine_iff AdicPoint.act_pt AdicPoint.lineC AdicPoint.vecCons_toOmega_mem coe_ofEq_apply coe_latticeMapEquiv_apply actBaseChange_tmul rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum lineBaseChange"
namespace T3Aux
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

section Injective

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}
  {C : Type} [Field C] [Algebra K C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]
  {ϖ : PseudoUniformizer K C}

theorem exists_act_inv_eq (hπ : Irreducible π) (M : FullLattice 𝒪 K) :
    ∃ g : GL (Fin 2) K, FullLattice.act g⁻¹ (stdFullLattice K) = M := by
  obtain ⟨g, hg⟩ := exists_act_eq hπ M
  exact ⟨g⁻¹, by rw [inv_inv]; exact hg⟩

theorem lineCoord_eq_of_toOmega_eq (hF : IsAdicFrame π ϖ R) (P Q : AdicPoint K π R)
    (h : P.toOmega C = Q.toOmega C) (n : ℕ) : lineCoord P n = lineCoord Q n := by
  obtain ⟨v, i₀, μ, hvi, hμ, hline, hvC⟩ := exists_limitVec hF P
  obtain ⟨v', i₀', μ', hvi', hμ', hline', hvC'⟩ := exists_limitVec hF Q
  rw [h] at hvC
  have hvCi : ∀ i, algebraMap R C (v i) = μ * vec (Q.toOmega C) 1 i := fun i => by
    have := congrFun hvC i; simpa only [Pi.smul_apply, smul_eq_mul] using this
  have hvCi' : ∀ i, algebraMap R C (v' i) = μ' * vec (Q.toOmega C) 1 i := fun i => by
    have := congrFun hvC' i; simpa only [Pi.smul_apply, smul_eq_mul] using this

  have hcross : ∀ i, algebraMap R C (v i) * μ' = algebraMap R C (v' i) * μ := fun i => by
    rw [hvCi, hvCi']; ring

  have h1 : ∀ j, v j = v i₀' * v' j := by
    intro j
    apply hF.injective
    rw [map_mul]
    have hc := hcross i₀'
    rw [hvi', map_one, one_mul] at hc

    apply mul_right_cancel₀ hμ'
    rw [hcross j, ← hc]; ring
  have h2 : ∀ j, v' j = v' i₀ * v j := by
    intro j
    apply hF.injective
    rw [map_mul]
    have hc := hcross i₀
    rw [hvi, map_one, one_mul] at hc

    apply mul_right_cancel₀ hμ
    rw [← hcross j, hc]; ring
  rw [hline n, hline' n]
  apply le_antisymm
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨Ideal.Quotient.mk _ (v i₀'), ?_⟩
    funext j; simp only [Pi.smul_apply, smul_eq_mul, ← map_mul, ← h1 j]
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨Ideal.Quotient.mk _ (v' i₀), ?_⟩
    funext j; simp only [Pi.smul_apply, smul_eq_mul, ← map_mul, ← h2 j]

end Injective
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"

end CerednikDrinfeld.FormalOmega.T3Aux
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.moebius Omega.pmoebius Omega.pmoebius_mk"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt DeligneDatum.InEdgeChart modPow span_pow_succ_le modPowTransition AdicPoint stdFullLattice stdBasisVec coordToTensor AdicPoint.mem_stdLine_iff AdicPoint.act_pt AdicPoint.lineC AdicPoint.vecCons_toOmega_mem coe_ofEq_apply coe_latticeMapEquiv_apply actBaseChange_tmul rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum lineBaseChange"
namespace T3Aux
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

open TensorProduct

section Residue

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}

theorem latticeMap_scalarGL_unit (u : 𝒪ˣ) (L : Submodule 𝒪 (Fin 2 → K)) (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K u) :
    latticeMap (scalarGL c) L = L := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    rw [mulVecLinR_apply, scalarGL_mulVec, hc, algebraMap_smul]
    exact L.smul_mem _ hv
  · intro v hv
    refine ⟨(algebraMap 𝒪 K ↑u⁻¹) • v, ?_, ?_⟩
    · rw [algebraMap_smul]; exact L.smul_mem _ hv
    · rw [mulVecLinR_apply, scalarGL_mulVec, hc, smul_smul, ← map_mul, Units.mul_inv, map_one, one_smul]

theorem scalarGL_mul' (a b : Kˣ) : scalarGL (a * b) = scalarGL a * scalarGL b := by
  apply Units.ext
  rw [Units.val_mul, scalarGL_coe, scalarGL_coe, scalarGL_coe, Units.val_mul, Matrix.smul_mul, Matrix.one_mul, smul_smul]

theorem adjacentLattice_iff_pi (hπ : Irreducible π) (L L' : Submodule 𝒪 (Fin 2 → K)) :
    AdjacentLattice L L' ↔ latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) L < L' ∧ L' < L := by
  constructor
  · rintro ⟨ϖ, hϖ, h1, h2⟩
    obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible _ hπ hϖ

    have hunits : (unitOfNeZero (K := K) hϖ.ne_zero : Kˣ) =
        unitOfNeZero (K := K) hπ.ne_zero * Units.map (algebraMap 𝒪 K : 𝒪 →* K) u := by
      apply Units.ext
      rw [Units.val_mul, unitOfNeZero_coe, unitOfNeZero_coe, Units.coe_map, MonoidHom.coe_coe, ← map_mul, hu]
    refine ⟨?_, h2⟩
    rw [hunits, scalarGL_mul', latticeMap_mul,
      latticeMap_scalarGL_unit u L _ (by rw [Units.coe_map, MonoidHom.coe_coe])] at h1
    exact h1
  · intro h
    exact ⟨π, hπ, h.1, h.2⟩

end Residue
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"

section HomothetyInv

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪} {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem map_mem_smul_top {X Y : Type} [AddCommGroup X] [Module B X] [AddCommGroup Y] [Module B Y]
    (f : X →ₗ[B] Y) (𝔭 : Ideal B) {p : X} (hp : p ∈ (𝔭 • ⊤ : Submodule B X)) : f p ∈ (𝔭 • ⊤ : Submodule B Y) := by
  refine Submodule.smul_induction_on (p := fun p => f p ∈ (𝔭 • ⊤ : Submodule B Y)) hp (fun r hr x _ => ?_)
    (fun x y hx hy => ?_)
  · show f (r • x) ∈ _
    rw [map_smul]; exact Submodule.smul_mem_smul hr Submodule.mem_top
  · show f (x + y) ∈ _
    rw [map_add]; exact add_mem hx hy

theorem one_tmul_mem_sup_act_iff (d : DeligneDatum (K := K) π B) (M : FullLattice 𝒪 K) (c : Kˣ) (𝔭 : Ideal B)
    (v : ↥M.1) :
    (1 : B) ⊗ₜ[𝒪] latticeMapEquiv (scalarGL c) M.1 v ∈
        d.line (FullLattice.act (scalarGL c) M) ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (FullLattice.act (scalarGL c) M))) ↔
      (1 : B) ⊗ₜ[𝒪] v ∈ d.line M ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)) := by
  have hA : (1 : B) ⊗ₜ[𝒪] latticeMapEquiv (scalarGL c) M.1 v = actBaseChange B (scalarGL c) M ((1 : B) ⊗ₜ[𝒪] v) := rfl
  rw [hA, d.homothety c M]
  constructor
  · intro h
    have h' : actBaseChange B (scalarGL c) M ((1 : B) ⊗ₜ[𝒪] v) ∈
        ((d.line M).map (actBaseChange B (scalarGL c) M).toLinearMap ⊔ (𝔭 • ⊤ : Submodule B _) :
          Submodule B (latticeBaseChange 𝒪 K B (FullLattice.act (scalarGL c) M))) := h
    obtain ⟨n', hn', p', hp', hsum⟩ := (Submodule.mem_sup (R := B)
      (M := latticeBaseChange 𝒪 K B (FullLattice.act (scalarGL c) M))).mp h'
    obtain ⟨n, hn, rfl⟩ := (Submodule.mem_map (R := B) (R₂ := B) (M := latticeBaseChange 𝒪 K B M)
      (M₂ := latticeBaseChange 𝒪 K B (FullLattice.act (scalarGL c) M))).mp hn'
    have key : (1 : B) ⊗ₜ[𝒪] v = n + (actBaseChange B (scalarGL c) M).symm p' := by
      apply (actBaseChange B (scalarGL c) M).injective
      rw [map_add, LinearEquiv.apply_symm_apply, ← hsum]; rfl
    rw [key]
    exact (Submodule.mem_sup (R := B) (M := latticeBaseChange 𝒪 K B M)).mpr
      ⟨n, hn, _, map_mem_smul_top (actBaseChange B (scalarGL c) M).symm.toLinearMap 𝔭 hp', rfl⟩
  · intro h
    obtain ⟨n, hn, p, hp, hsum⟩ := (Submodule.mem_sup (R := B) (M := latticeBaseChange 𝒪 K B M)).mp h
    rw [← hsum, map_add]
    exact (Submodule.mem_sup (R := B) (M := latticeBaseChange 𝒪 K B (FullLattice.act (scalarGL c) M))).mpr
      ⟨_, Submodule.mem_map_of_mem hn, _, map_mem_smul_top (actBaseChange B (scalarGL c) M).toLinearMap 𝔭 hp, rfl⟩

theorem smul_mem_act_iff (c : Kˣ) (L : FullLattice 𝒪 K) (w : Fin 2 → K) :
    (c : K) • w ∈ (FullLattice.act (scalarGL c) L).1 ↔ w ∈ L.1 := by
  constructor
  · rintro ⟨v, hv, h⟩
    rw [mulVecLinR_apply, scalarGL_mulVec] at h
    rwa [← smul_right_injective (Fin 2 → K) c.ne_zero h]
  · intro h
    exact ⟨w, h, by rw [mulVecLinR_apply, scalarGL_mulVec]⟩

theorem exists_eq_smul_of_mem_act (c : Kˣ) (L : FullLattice 𝒪 K) (w : Fin 2 → K)
    (hw : w ∈ (FullLattice.act (scalarGL c) L).1) : ∃ v ∈ L.1, w = (c : K) • v := by
  obtain ⟨v, hv, h⟩ := hw
  exact ⟨v, hv, by rw [← h, mulVecLinR_apply, scalarGL_mulVec]⟩

theorem coe_latticeMapEquiv_scalarGL (c : Kˣ) (L : FullLattice 𝒪 K) (v : ↥L.1) :
    ((latticeMapEquiv (scalarGL c) L.1 v) : Fin 2 → K) = (c : K) • (v : Fin 2 → K) := by
  rw [coe_latticeMapEquiv_apply, scalarGL_mulVec]

theorem forall_act_iff (c : Kˣ) (L : FullLattice 𝒪 K) (P : ↥(FullLattice.act (scalarGL c) L).1 → Prop) :
    (∀ w, P w) ↔ ∀ v : ↥L.1, P (latticeMapEquiv (scalarGL c) L.1 v) := by
  constructor
  · intro h v; exact h _
  · intro h w
    obtain ⟨v, hv, hw⟩ := exists_eq_smul_of_mem_act c L w w.2
    have : w = latticeMapEquiv (scalarGL c) L.1 ⟨v, hv⟩ := by
      apply Subtype.ext; rw [coe_latticeMapEquiv_scalarGL]; exact hw
    rw [this]; exact h _

theorem inEdgeChart_act_scalarGL_iff' (d : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K) (c : Kˣ) :
    d.InEdgeChart π (FullLattice.act (scalarGL c) M') (FullLattice.act (scalarGL c) M) ↔ d.InEdgeChart π M' M := by
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  unfold DeligneDatum.InEdgeChart DeligneDatum.EdgeNondegAt
  refine forall_congr' fun 𝔭 => imp_congr_right fun _ => ?_
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  ·
    constructor
    · intro h v hv
      have := h ((smul_mem_act_iff c M' v).mpr hv)
      exact (smul_mem_act_iff c M v).mp this
    · intro h w hw
      obtain ⟨v, hv, rfl⟩ := exists_eq_smul_of_mem_act c M' w hw
      exact (smul_mem_act_iff c M v).mpr (h hv)
  ·
    rw [forall_act_iff c M]
    refine forall_congr' fun v => ?_
    rw [coe_latticeMapEquiv_scalarGL, smul_comm, smul_mem_act_iff]
  · rw [forall_act_iff c M]
    refine forall_congr' fun v => imp_congr (not_congr ?_) (not_congr (one_tmul_mem_sup_act_iff d M c 𝔭 v))
    rw [coe_latticeMapEquiv_scalarGL, smul_mem_act_iff]
  · rw [forall_act_iff c M']
    refine forall_congr' fun v' => imp_congr (not_congr ?_) (not_congr (one_tmul_mem_sup_act_iff d M' c 𝔭 v'))
    rw [coe_latticeMapEquiv_scalarGL]
    constructor
    · rintro ⟨w, hw⟩
      obtain ⟨w₀, hw₀, hw₀'⟩ := exists_eq_smul_of_mem_act c M w w.2
      refine ⟨⟨w₀, hw₀⟩, smul_right_injective (Fin 2 → K) hc0 ?_⟩
      show (c : K) • (v' : Fin 2 → K) = (c : K) • ((algebraMap 𝒪 K π) • w₀)
      rw [hw, hw₀', smul_comm]
    · rintro ⟨w₀, hw₀⟩
      refine ⟨⟨(c : K) • (w₀ : Fin 2 → K), (smul_mem_act_iff c M _).mpr w₀.2⟩, ?_⟩
      show (c : K) • (v' : Fin 2 → K) = (algebraMap 𝒪 K π) • ((c : K) • (w₀ : Fin 2 → K))
      rw [hw₀, smul_comm]

end HomothetyInv
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"

end CerednikDrinfeld.FormalOmega.T3Aux
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.moebius Omega.pmoebius Omega.pmoebius_mk"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt DeligneDatum.InEdgeChart modPow span_pow_succ_le modPowTransition AdicPoint stdFullLattice stdBasisVec coordToTensor AdicPoint.mem_stdLine_iff AdicPoint.act_pt AdicPoint.lineC AdicPoint.vecCons_toOmega_mem coe_ofEq_apply coe_latticeMapEquiv_apply actBaseChange_tmul rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum lineBaseChange"
namespace T3Aux
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

open TensorProduct

section ResidueField

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}

theorem isMaximal_span (hπ : Irreducible π) : (Ideal.span {π} : Ideal 𝒪).IsMaximal := by
  rw [← hπ.maximalIdeal_eq]; exact IsLocalRing.maximalIdeal.isMaximal 𝒪

theorem exists_one_tmul {I : Ideal 𝒪} (M : FullLattice 𝒪 K) (y : latticeBaseChange 𝒪 K (𝒪 ⧸ I) M) :
    ∃ v : ↥M.1, y = (1 : 𝒪 ⧸ I) ⊗ₜ[𝒪] v := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, (tmul_zero _ _).symm⟩
  | tmul a v =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨r • v, ?_⟩
    rw [tmul_smul, ← algebraMap_smul (𝒪 ⧸ I) r, smul_tmul', smul_eq_mul, mul_one, Ideal.Quotient.algebraMap_eq]
  | add x y hx hy =>
    obtain ⟨v, rfl⟩ := hx; obtain ⟨w, rfl⟩ := hy
    exact ⟨v + w, (tmul_add _ _ _).symm⟩

open Pointwise in

theorem one_tmul_eq_zero_iff (M : FullLattice 𝒪 K) (v : ↥M.1) :
    (1 : 𝒪 ⧸ Ideal.span {π}) ⊗ₜ[𝒪] v = 0 ↔ ∃ w : ↥M.1, (v : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K) := by
  have key : (1 : 𝒪 ⧸ Ideal.span {π}) ⊗ₜ[𝒪] v = 0 ↔ v ∈ (π • ⊤ : Submodule 𝒪 ↥M.1) := by
    rw [← (TensorProduct.quotTensorEquivQuotSMul (↥M.1) (Ideal.span {π})).map_eq_zero_iff,
      ← map_one (Ideal.Quotient.mk (Ideal.span {π})), TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul,
      Submodule.Quotient.mk_eq_zero, Submodule.ideal_span_singleton_smul]
  rw [key, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, -, hw⟩
    exact ⟨w, by rw [← hw, Submodule.coe_smul, algebraMap_smul]⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, Submodule.mem_top, (Subtype.ext (by rw [Submodule.coe_smul, hw, algebraMap_smul])).symm⟩

theorem line_ne_bot (hπ : Irreducible π) (d : DeligneDatum (K := K) π (𝒪 ⧸ Ideal.span {π})) (M : FullLattice 𝒪 K) :
    d.line M ≠ ⊥ := by
  classical
  haveI := isMaximal_span hπ
  letI : Field (𝒪 ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  haveI : IsLocalRing (𝒪 ⧸ Ideal.span {π}) := inferInstance
  obtain ⟨b⟩ := exists_basis hπ M
  let e : latticeBaseChange 𝒪 K (𝒪 ⧸ Ideal.span {π}) M ≃ₗ[𝒪 ⧸ Ideal.span {π}] (Fin 2 → 𝒪 ⧸ Ideal.span {π}) :=
    (b.baseChange (𝒪 ⧸ Ideal.span {π})).equivFun
  haveI := d.invertible M
  haveI : Module.Invertible (𝒪 ⧸ Ideal.span {π}) ((Fin 2 → 𝒪 ⧸ Ideal.span {π}) ⧸ (d.line M).map e.toLinearMap) :=
    Module.Invertible.congr (Submodule.Quotient.equiv _ _ e rfl)
  intro hbot
  rcases exists_eq_span_of_invertible ((d.line M).map e.toLinearMap) with ⟨c, hc⟩ | ⟨c, hc⟩
  · have hm : (vec 1 c : Fin 2 → 𝒪 ⧸ Ideal.span {π}) ∈ (d.line M).map e.toLinearMap :=
      hc ▸ Submodule.mem_span_singleton_self _
    rw [hbot, Submodule.map_bot, Submodule.mem_bot] at hm
    have := congrFun hm 0
    simp at this
  · have hm : (vec c 1 : Fin 2 → 𝒪 ⧸ Ideal.span {π}) ∈ (d.line M).map e.toLinearMap :=
      hc ▸ Submodule.mem_span_singleton_self _
    rw [hbot, Submodule.map_bot, Submodule.mem_bot] at hm
    have := congrFun hm 1
    simp at this

theorem edgeNondegAt_bot_of_inEdgeChart (hπ : Irreducible π) (d : DeligneDatum (K := K) π (𝒪 ⧸ Ideal.span {π}))
    (M' M : FullLattice 𝒪 K) (h : d.InEdgeChart π M' M) : d.EdgeNondegAt π ⊥ M' M := by
  haveI := isMaximal_span hπ
  letI : Field (𝒪 ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  exact h ⊥ Ideal.bot_prime

theorem sup_bot_smul_top {k : Type} [CommRing k] {X : Type} [AddCommGroup X] [Module k X] (N : Submodule k X) :
    N ⊔ ((⊥ : Ideal k) • ⊤ : Submodule k X) = N := by
  rw [Submodule.bot_smul, sup_bot_eq]

theorem adjacentLattice_of_inEdgeChart_residue' (hπ : Irreducible π)
    (d : DeligneDatum (K := K) π (𝒪 ⧸ Ideal.span {π})) (M' M : FullLattice 𝒪 K) (h : d.InEdgeChart π M' M) :
    AdjacentLattice M.1 M'.1 := by
  obtain ⟨hle, hπM, h1, h2⟩ := edgeNondegAt_bot_of_inEdgeChart hπ d M' M h
  rw [adjacentLattice_iff_pi hπ]
  constructor
  ·
    refine lt_of_le_of_ne ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      rw [mulVecLinR_apply, scalarGL_mulVec, unitOfNeZero_coe]
      exact hπM ⟨v, hv⟩
    · intro heq

      apply line_ne_bot hπ d M
      rw [eq_bot_iff]
      intro n hn
      obtain ⟨v, rfl⟩ := exists_one_tmul M n
      by_contra hne
      have hv : (v : Fin 2 → K) ∉ M'.1 := by
        intro hvM'
        rw [← heq] at hvM'
        obtain ⟨w, hw, hwv⟩ := hvM'
        rw [mulVecLinR_apply, scalarGL_mulVec, unitOfNeZero_coe] at hwv
        exact hne ((one_tmul_eq_zero_iff M v).mpr ⟨⟨w, hw⟩, hwv.symm⟩)
      exact h1 v hv (by rw [sup_bot_smul_top]; exact hn)
  ·
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply line_ne_bot hπ d M'
    rw [eq_bot_iff]
    intro n hn
    obtain ⟨v', rfl⟩ := exists_one_tmul M' n
    by_contra hne
    have hv' : ¬ ∃ w : ↥M.1, (v' : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K) := by
      rintro ⟨w, hw⟩
      have hwM' : (w : Fin 2 → K) ∈ M'.1 := by rw [heq]; exact w.2
      exact hne ((one_tmul_eq_zero_iff M' v').mpr ⟨⟨w, hwM'⟩, hw⟩)
    exact h2 v' hv' (by rw [sup_bot_smul_top]; exact hn)

end ResidueField
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"

end CerednikDrinfeld.FormalOmega.T3Aux
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.moebius Omega.pmoebius Omega.pmoebius_mk"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt DeligneDatum.InEdgeChart modPow span_pow_succ_le modPowTransition AdicPoint stdFullLattice stdBasisVec coordToTensor AdicPoint.mem_stdLine_iff AdicPoint.act_pt AdicPoint.lineC AdicPoint.vecCons_toOmega_mem coe_ofEq_apply coe_latticeMapEquiv_apply actBaseChange_tmul rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum lineBaseChange"
namespace ChainAux
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

open CerednikDrinfeld.FormalOmega.T3Aux

section

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}

theorem unit_zpow_decomp (hπ : Irreducible π) (c : Kˣ) :
    ∃ (u : 𝒪ˣ) (j : ℤ), c = Units.map (algebraMap 𝒪 K : 𝒪 →* K) u * (unitOfNeZero (K := K) hπ.ne_zero) ^ j := by
  have hπK : algebraMap 𝒪 K π ≠ 0 := algebraMap_ne_zero' hπ
  obtain ⟨a, b, hb, hc⟩ := IsFractionRing.div_surjective (A := 𝒪) (c : K)
  have hbz : (b : 𝒪) ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap 𝒪 K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective 𝒪 K)).2 hbz
  have haz : a ≠ 0 := by
    intro ha
    apply c.ne_zero
    rw [← hc, ha, map_zero, zero_div]
  obtain ⟨m, u₁, hu₁⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible haz hπ
  obtain ⟨n, u₂, hu₂⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hbz hπ
  refine ⟨u₁ * u₂⁻¹, (m : ℤ) - (n : ℤ), Units.ext ?_⟩
  rw [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.val_zpow_eq_zpow_val, unitOfNeZero_coe, ← hc, hu₁, hu₂,
    zpow_sub₀ hπK, zpow_natCast, zpow_natCast, map_mul, map_mul, map_pow, map_pow, Units.val_mul, map_mul,
    map_units_inv]
  have hu₂K : algebraMap 𝒪 K (u₂ : 𝒪) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective 𝒪 K)).2 u₂.ne_zero
  field_simp

def chainLat (hπ : Irreducible π) (M' M : FullLattice 𝒪 K) (n : ℤ) : Submodule 𝒪 (Fin 2 → K) :=
  latticeMap (scalarGL ((unitOfNeZero (K := K) hπ.ne_zero) ^ (n / 2))) (if n % 2 = 0 then M.1 else M'.1)

theorem chainLat_two_mul (hπ : Irreducible π) (M' M : FullLattice 𝒪 K) (j : ℤ) :
    chainLat hπ M' M (2 * j) = latticeMap (scalarGL ((unitOfNeZero (K := K) hπ.ne_zero) ^ j)) M.1 := by
  have h1 : (2 * j) / 2 = j := by omega
  have h2 : (2 * j) % 2 = 0 := by omega
  rw [chainLat, h1, if_pos h2]

theorem chainLat_two_mul_add_one (hπ : Irreducible π) (M' M : FullLattice 𝒪 K) (j : ℤ) :
    chainLat hπ M' M (2 * j + 1) = latticeMap (scalarGL ((unitOfNeZero (K := K) hπ.ne_zero) ^ j)) M'.1 := by
  have h1 : (2 * j + 1) / 2 = j := by omega
  have h2 : ¬ (2 * j + 1) % 2 = 0 := by omega
  rw [chainLat, h1, if_neg h2]

theorem latticeMap_scalarGL_mul (a b : Kˣ) (X : Submodule 𝒪 (Fin 2 → K)) :
    latticeMap (scalarGL a) (latticeMap (scalarGL b) X) = latticeMap (scalarGL (a * b)) X := by
  rw [scalarGL_mul', latticeMap_mul]

theorem latticeMap_zpow_chainLat (hπ : Irreducible π) (M' M : FullLattice 𝒪 K) (j n : ℤ) :
    latticeMap (scalarGL ((unitOfNeZero (K := K) hπ.ne_zero) ^ j)) (chainLat hπ M' M n) = chainLat hπ M' M (n + 2 * j) := by
  have h1 : (n + 2 * j) / 2 = n / 2 + j := by omega
  have h2 : (n + 2 * j) % 2 = n % 2 := by omega
  rw [chainLat, chainLat, h1, h2, latticeMap_scalarGL_mul, ← zpow_add, add_comm j]

theorem chainLat_add_two (hπ : Irreducible π) (M' M : FullLattice 𝒪 K) (n : ℤ) :
    chainLat hπ M' M (n + 2) = latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) (chainLat hπ M' M n) := by
  have := latticeMap_zpow_chainLat hπ M' M 1 n
  rw [zpow_one, mul_one] at this
  exact this.symm

theorem latticeMap_units_chainLat (hπ : Irreducible π) (M' M : FullLattice 𝒪 K) (w : 𝒪ˣ) (n : ℤ) :
    latticeMap (scalarGL (Units.map (algebraMap 𝒪 K : 𝒪 →* K) w)) (chainLat hπ M' M n) = chainLat hπ M' M n := by
  unfold chainLat
  exact latticeMap_scalarGL_unit w _ _ (by rw [Units.coe_map, MonoidHom.coe_coe])

theorem isFullLattice_chainLat (hπ : Irreducible π) (M' M : FullLattice 𝒪 K) (n : ℤ) :
    IsFullLattice (chainLat hπ M' M n) := by
  unfold chainLat
  split_ifs
  · exact M.2.map _
  · exact M'.2.map _

theorem chainLat_succ_lt (hπ : Irreducible π) (M' M : FullLattice 𝒪 K) (hadj : AdjacentLattice M.1 M'.1) (n : ℤ) :
    chainLat hπ M' M (n + 1) < chainLat hπ M' M n := by
  obtain ⟨h1, h2⟩ := (adjacentLattice_iff_pi hπ M.1 M'.1).1 hadj
  rcases Int.emod_two_eq_zero_or_one n with hn | hn
  ·
    have hj : n = 2 * (n / 2) := by omega
    have e1 : n + 1 = 2 * (n / 2) + 1 := by omega
    rw [e1, chainLat_two_mul_add_one]
    conv_rhs => rw [hj, chainLat_two_mul]
    exact (latticeMap_lt_latticeMap_iff _).2 h2
  ·
    have hj : n = 2 * (n / 2) + 1 := by omega
    have e1 : n + 1 = 2 * (n / 2 + 1) := by omega
    rw [e1, chainLat_two_mul, zpow_add_one, ← latticeMap_scalarGL_mul]
    conv_rhs => rw [hj, chainLat_two_mul_add_one]
    exact (latticeMap_lt_latticeMap_iff _).2 h1

theorem chainLat_strictAnti (hπ : Irreducible π) (M' M : FullLattice 𝒪 K) (hadj : AdjacentLattice M.1 M'.1) :
    StrictAnti (chainLat hπ M' M) :=
  strictAnti_int_of_succ_lt fun n => chainLat_succ_lt hπ M' M hadj n

theorem chainLat_antitone (hπ : Irreducible π) (M' M : FullLattice 𝒪 K) (hadj : AdjacentLattice M.1 M'.1) :
    Antitone (chainLat hπ M' M) :=
  (chainLat_strictAnti hπ M' M hadj).antitone

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"

end CerednikDrinfeld.FormalOmega.ChainAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux"

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪}
    {C : Type} [Field C] [Algebra K C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]
    (ϖ : PseudoUniformizer K C) (hF : IsAdicFrame π ϖ R) (a : K) (ha : a ≠ 0) :
    ∃ k : ℤ, Valued.v (algebraMap K C a) = Valued.v (algebraMap K C ϖ.ϖ) ^ k := by
  classical
  have hπ := hF.irreducible
  obtain ⟨u, j, hu⟩ := CerednikDrinfeld.FormalOmega.ChainAux.unit_zpow_decomp (K := K) hπ (Units.mk0 a ha)
  have ha' : a = algebraMap 𝒪 K (u : 𝒪) * (algebraMap 𝒪 K π) ^ j := by
    have := congrArg Units.val hu
    rw [Units.val_mk0, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.val_zpow_eq_zpow_val, unitOfNeZero_coe] at this
    exact this

  have hvu : Valued.v (algebraMap K C (algebraMap 𝒪 K (u : 𝒪))) = 1 := by
    have hle : ∀ b : 𝒪, Valued.v (algebraMap K C (algebraMap 𝒪 K b)) ≤ 1 := fun b => (hF.integers _).2 ⟨b, rfl⟩
    apply le_antisymm (hle _)
    by_contra hlt
    have h1 : Valued.v (algebraMap K C (algebraMap 𝒪 K (u : 𝒪))) * Valued.v (algebraMap K C (algebraMap 𝒪 K (↑u⁻¹ : 𝒪))) = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, map_one]
    have : Valued.v (algebraMap K C (algebraMap 𝒪 K (u : 𝒪))) * Valued.v (algebraMap K C (algebraMap 𝒪 K (↑u⁻¹ : 𝒪))) < 1 :=
      mul_lt_one_of_lt_of_le (not_le.mp hlt) (hle _)
    rw [h1] at this
    exact lt_irrefl _ this
  have hπϖ : algebraMap K C (algebraMap 𝒪 K π) = algebraMap K C ϖ.ϖ := by
    rw [← IsScalarTower.algebraMap_apply 𝒪 K C]; exact hF.unif
  refine ⟨j, ?_⟩
  rw [ha', map_mul, map_zpow₀, map_mul, map_zpow₀, hvu, one_mul, hπϖ]

end S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow (solution)
