-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.AdicPoint.inEdgeChart_iff_toOmega_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/7a6e160b-f78e-5107-bb4e-70d01ef65d75

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_act
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
p2m_open "LT.LatticeTree CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "FormalOmega.AdicPoint tree Omega.mem_stdEdgeTube_iff Omega.vertexTube Omega.edgeTube Omega.mem_vertexTube_iff Omega.mem_edgeTube_iff Omega.pmoebius Omega.upperHalfPlane Omega.pmoebius_mem_upperHalfPlane Omega.pmoebius_one Omega.pmoebius_mul FormalOmega.AdicPoint.toOmega_act FormalOmega.AdicPoint.toOmega_mem_upperHalfPlane"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt DeligneDatum.InVertexChart DeligneDatum.InEdgeChart modPow span_pow_succ_le modPowTransition AdicPoint stdFullLattice stdBasisVec coordToTensor AdicPoint.mem_stdLine_iff AdicPoint.act_pt AdicPoint.lineC AdicPoint.vecCons_toOmega_mem edgeFlip_ne_zero edgeFlip edgeFlip_mulVec pmoebius_edgeFlip coe_ofEq_apply coe_latticeMapEquiv_apply actBaseChange_tmul DeligneDatum.pullback rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum lineBaseChange AdicPoint.toOmega_act AdicPoint.toOmega_mem_upperHalfPlane"
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
p2m_export "CerednikDrinfeld" "FormalOmega.AdicPoint tree Omega.mem_stdEdgeTube_iff Omega.vertexTube Omega.edgeTube Omega.mem_vertexTube_iff Omega.mem_edgeTube_iff Omega.pmoebius Omega.upperHalfPlane Omega.pmoebius_mem_upperHalfPlane Omega.pmoebius_one Omega.pmoebius_mul FormalOmega.AdicPoint.toOmega_act FormalOmega.AdicPoint.toOmega_mem_upperHalfPlane"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt DeligneDatum.InVertexChart DeligneDatum.InEdgeChart modPow span_pow_succ_le modPowTransition AdicPoint stdFullLattice stdBasisVec coordToTensor AdicPoint.mem_stdLine_iff AdicPoint.act_pt AdicPoint.lineC AdicPoint.vecCons_toOmega_mem edgeFlip_ne_zero edgeFlip edgeFlip_mulVec pmoebius_edgeFlip coe_ofEq_apply coe_latticeMapEquiv_apply actBaseChange_tmul DeligneDatum.pullback rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum lineBaseChange AdicPoint.toOmega_act AdicPoint.toOmega_mem_upperHalfPlane"
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
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "FormalOmega.AdicPoint tree Omega.mem_stdEdgeTube_iff Omega.vertexTube Omega.edgeTube Omega.mem_vertexTube_iff Omega.mem_edgeTube_iff Omega.pmoebius Omega.upperHalfPlane Omega.pmoebius_mem_upperHalfPlane Omega.pmoebius_one Omega.pmoebius_mul FormalOmega.AdicPoint.toOmega_act FormalOmega.AdicPoint.toOmega_mem_upperHalfPlane"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt DeligneDatum.InVertexChart DeligneDatum.InEdgeChart modPow span_pow_succ_le modPowTransition AdicPoint stdFullLattice stdBasisVec coordToTensor AdicPoint.mem_stdLine_iff AdicPoint.act_pt AdicPoint.lineC AdicPoint.vecCons_toOmega_mem edgeFlip_ne_zero edgeFlip edgeFlip_mulVec pmoebius_edgeFlip coe_ofEq_apply coe_latticeMapEquiv_apply actBaseChange_tmul DeligneDatum.pullback rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum lineBaseChange AdicPoint.toOmega_act AdicPoint.toOmega_mem_upperHalfPlane"
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
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"

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
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"

end CerednikDrinfeld.FormalOmega.T2aAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "FormalOmega.AdicPoint tree Omega.mem_stdEdgeTube_iff Omega.vertexTube Omega.edgeTube Omega.mem_vertexTube_iff Omega.mem_edgeTube_iff Omega.pmoebius Omega.upperHalfPlane Omega.pmoebius_mem_upperHalfPlane Omega.pmoebius_one Omega.pmoebius_mul FormalOmega.AdicPoint.toOmega_act FormalOmega.AdicPoint.toOmega_mem_upperHalfPlane"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt DeligneDatum.InVertexChart DeligneDatum.InEdgeChart modPow span_pow_succ_le modPowTransition AdicPoint stdFullLattice stdBasisVec coordToTensor AdicPoint.mem_stdLine_iff AdicPoint.act_pt AdicPoint.lineC AdicPoint.vecCons_toOmega_mem edgeFlip_ne_zero edgeFlip edgeFlip_mulVec pmoebius_edgeFlip coe_ofEq_apply coe_latticeMapEquiv_apply actBaseChange_tmul DeligneDatum.pullback rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum lineBaseChange AdicPoint.toOmega_act AdicPoint.toOmega_mem_upperHalfPlane"
namespace T4VAux
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

open TensorProduct

section Transport

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem map_mem_smul_top {P Q : Type} [AddCommGroup P] [Module B P] [AddCommGroup Q] [Module B Q]
    (I : Ideal B) (f : P →ₗ[B] Q) {z : P} (hz : z ∈ (I • ⊤ : Submodule B P)) : f z ∈ (I • ⊤ : Submodule B Q) := by
  have h : (I • ⊤ : Submodule B P).map f ≤ I • ⊤ := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact h (Submodule.mem_map_of_mem hz)

theorem mem_comap_sup_smul_top_iff {M₁ M₂ : Type} [AddCommGroup M₁] [Module B M₁] [AddCommGroup M₂] [Module B M₂]
    (e : M₁ ≃ₗ[B] M₂) (N : Submodule B M₂) (I : Ideal B) (x : M₁) :
    x ∈ N.comap e.toLinearMap ⊔ (I • ⊤ : Submodule B M₁) ↔ e x ∈ N ⊔ (I • ⊤ : Submodule B M₂) := by
  constructor
  · intro hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.mem_sup.2 ⟨e y, Submodule.mem_comap.1 hy, e z, map_mem_smul_top I e.toLinearMap hz, rfl⟩
  · intro hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hx
    have hx' : x = e.symm y + e.symm z := by
      rw [← map_add, hyz, LinearEquiv.symm_apply_apply]
    rw [hx']
    refine Submodule.mem_sup.2 ⟨e.symm y, ?_, e.symm z, map_mem_smul_top I e.symm.toLinearMap hz, rfl⟩
    simpa [Submodule.mem_comap] using hy

theorem not_exists_eq_smul_latticeMapEquiv_iff (g : GL (Fin 2) K) (M : FullLattice 𝒪 K) (v : ↥M.1) :
    (¬ ∃ w : ↥(FullLattice.act g M).1,
        ((latticeMapEquiv g M.1 v : ↥(FullLattice.act g M).1) : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K)) ↔
      ¬ ∃ w : ↥M.1, (v : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K) := by
  refine not_congr ⟨?_, ?_⟩
  · rintro ⟨w', hw'⟩
    obtain ⟨w, rfl⟩ := (latticeMapEquiv g M.1).surjective w'
    refine ⟨w, ?_⟩
    rw [coe_latticeMapEquiv_apply, coe_latticeMapEquiv_apply, ← Matrix.mulVec_smul] at hw'
    have h := congrArg (fun x => Matrix.mulVec ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) x) hw'
    simpa only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] using h
  · rintro ⟨w, hw⟩
    refine ⟨latticeMapEquiv g M.1 w, ?_⟩
    rw [coe_latticeMapEquiv_apply, coe_latticeMapEquiv_apply, hw, Matrix.mulVec_smul]

theorem vertexNondegAt_pullback_iff (g : GL (Fin 2) K) (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B)
    (M : FullLattice 𝒪 K) :
    (DeligneDatum.pullback π B g d).VertexNondegAt π 𝔭 M ↔ d.VertexNondegAt π 𝔭 (FullLattice.act g M) := by
  unfold DeligneDatum.VertexNondegAt
  constructor
  · intro h v' hv'
    obtain ⟨v, rfl⟩ := (latticeMapEquiv g M.1).surjective v'
    have h1 := h v ((not_exists_eq_smul_latticeMapEquiv_iff g M v).1 hv')
    intro hmem
    apply h1
    show (1 : B) ⊗ₜ[𝒪] v ∈ (d.line (FullLattice.act g M)).comap (actBaseChange B g M).toLinearMap ⊔ (𝔭 • ⊤)
    rw [mem_comap_sup_smul_top_iff, actBaseChange_tmul]
    exact hmem
  · intro h v hv hmem
    have h1 := h (latticeMapEquiv g M.1 v) ((not_exists_eq_smul_latticeMapEquiv_iff g M v).2 hv)
    apply h1
    change (1 : B) ⊗ₜ[𝒪] v ∈ (d.line (FullLattice.act g M)).comap (actBaseChange B g M).toLinearMap ⊔ (𝔭 • ⊤) at hmem
    rw [mem_comap_sup_smul_top_iff, actBaseChange_tmul] at hmem
    exact hmem

theorem inVertexChart_pullback_iff (g : GL (Fin 2) K) (d : DeligneDatum (K := K) π B) (M : FullLattice 𝒪 K) :
    (DeligneDatum.pullback π B g d).InVertexChart π M ↔ d.InVertexChart π (FullLattice.act g M) := by
  unfold DeligneDatum.InVertexChart
  exact forall_congr' fun 𝔭 => forall_congr' fun _ => vertexNondegAt_pullback_iff g d 𝔭 M

end Transport
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"

end CerednikDrinfeld.FormalOmega.T4VAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "FormalOmega.AdicPoint tree Omega.mem_stdEdgeTube_iff Omega.vertexTube Omega.edgeTube Omega.mem_vertexTube_iff Omega.mem_edgeTube_iff Omega.pmoebius Omega.upperHalfPlane Omega.pmoebius_mem_upperHalfPlane Omega.pmoebius_one Omega.pmoebius_mul FormalOmega.AdicPoint.toOmega_act FormalOmega.AdicPoint.toOmega_mem_upperHalfPlane"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt DeligneDatum.InVertexChart DeligneDatum.InEdgeChart modPow span_pow_succ_le modPowTransition AdicPoint stdFullLattice stdBasisVec coordToTensor AdicPoint.mem_stdLine_iff AdicPoint.act_pt AdicPoint.lineC AdicPoint.vecCons_toOmega_mem edgeFlip_ne_zero edgeFlip edgeFlip_mulVec pmoebius_edgeFlip coe_ofEq_apply coe_latticeMapEquiv_apply actBaseChange_tmul DeligneDatum.pullback rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum lineBaseChange AdicPoint.toOmega_act AdicPoint.toOmega_mem_upperHalfPlane"
namespace T4VAux
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

open TensorProduct CerednikDrinfeld.FormalOmega.T2aAux CerednikDrinfeld.FormalOmega.LevelAux

section VecHelpers

variable {B : Type} [CommRing B]

theorem mem_smul_top_pi_iff (I : Ideal B) (z : Fin 2 → B) :
    z ∈ (I • ⊤ : Submodule B (Fin 2 → B)) ↔ z 0 ∈ I ∧ z 1 ∈ I := by
  constructor
  · intro hz
    refine Submodule.smul_induction_on hz (fun r hr n _ => ?_) (fun x y hx hy => ?_)
    · exact ⟨by simpa using I.mul_mem_right (n 0) hr, by simpa using I.mul_mem_right (n 1) hr⟩
    · exact ⟨by simpa using I.add_mem hx.1 hy.1, by simpa using I.add_mem hx.2 hy.2⟩
  · rintro ⟨h0, h1⟩
    rw [eq_vec z, vec]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul h0 Submodule.mem_top)
      (Submodule.smul_mem_smul h1 Submodule.mem_top)

theorem vec_add_vec (a b a' b' : B) : vec a b + vec a' b' = vec (a + a') (b + b') := by
  rw [eq_vec (vec a b + vec a' b')]
  simp

theorem vec_mem_span_vec_one_sup_iff (c a b : B) (I : Ideal B) :
    vec a b ∈ Submodule.span B {vec c 1} ⊔ (I • ⊤ : Submodule B (Fin 2 → B)) ↔ a - b * c ∈ I := by
  constructor
  · intro h
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [mem_smul_top_pi_iff] at hz
    have h0 := congrFun hyz 0
    have h1 := congrFun hyz 1
    simp only [Pi.add_apply, smul_vec, vec_apply_zero, vec_apply_one, mul_one] at h0 h1
    have : a - b * c = z 0 - z 1 * c := by rw [← h0, ← h1]; ring
    rw [this]
    exact I.sub_mem hz.1 (I.mul_mem_right _ hz.2)
  · intro h
    have : vec a b = b • vec c 1 + vec (a - b * c) 0 := by
      rw [smul_vec, vec_add_vec]; congr 1 <;> ring
    rw [this]
    exact Submodule.mem_sup.2 ⟨b • vec c 1, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),
      vec (a - b * c) 0, (mem_smul_top_pi_iff I _).2 ⟨by simpa using h, by simp⟩, rfl⟩

theorem vec_one_zero_mem_span_sup (c : B) (I : Ideal B) (hc : c ∈ I) :
    vec 1 0 ∈ Submodule.span B {vec 1 c} ⊔ (I • ⊤ : Submodule B (Fin 2 → B)) := by
  have : vec (1 : B) 0 = vec 1 c + vec 0 (-c) := by rw [vec_add_vec]; simp
  rw [this]
  exact Submodule.mem_sup.2 ⟨vec 1 c, Submodule.mem_span_singleton_self _, vec 0 (-c),
    (mem_smul_top_pi_iff I _).2 ⟨by simp, by simpa using I.neg_mem hc⟩, rfl⟩

theorem mem_sup_smul_top_iff_map {M₁ M₂ : Type} [AddCommGroup M₁] [Module B M₁] [AddCommGroup M₂] [Module B M₂]
    (e : M₁ ≃ₗ[B] M₂) (N : Submodule B M₁) (I : Ideal B) (x : M₁) :
    x ∈ N ⊔ (I • ⊤ : Submodule B M₁) ↔ e x ∈ N.map e.toLinearMap ⊔ (I • ⊤ : Submodule B M₂) := by
  rw [← mem_comap_sup_smul_top_iff e (N.map e.toLinearMap) I x, Submodule.comap_map_eq_of_injective]
  exact e.injective

end VecHelpers
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"

section FrameHelpers

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}
  {C : Type} [Field C] [Algebra K C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]
  {ϖ : PseudoUniformizer K C}

theorem v_algebraMap_int_le_one (hF : IsAdicFrame π ϖ R) (a : 𝒪) : Valued.v (algebraMap 𝒪 C a) ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply 𝒪 K C]
  exact (hF.integers _).2 ⟨a, rfl⟩

theorem v_algebraMap_unit_eq_one (hF : IsAdicFrame π ϖ R) {a : 𝒪} (ha : IsUnit a) : Valued.v (algebraMap 𝒪 C a) = 1 := by
  obtain ⟨u, rfl⟩ := ha
  apply le_antisymm (v_algebraMap_int_le_one hF _)
  by_contra hlt
  have h1 : Valued.v (algebraMap 𝒪 C (u : 𝒪)) * Valued.v (algebraMap 𝒪 C (↑u⁻¹ : 𝒪)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have : Valued.v (algebraMap 𝒪 C (u : 𝒪)) * Valued.v (algebraMap 𝒪 C (↑u⁻¹ : 𝒪)) < 1 :=
    mul_lt_one_of_lt_of_le (not_le.mp hlt) (v_algebraMap_int_le_one hF _)
  rw [h1] at this
  exact lt_irrefl _ this

theorem isUnit_of_not_dvd (hπ : Irreducible π) {a : 𝒪} (ha : ¬ π ∣ a) : IsUnit a := by
  by_contra hu
  apply ha
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ
  have : a ∈ IsLocalRing.maximalIdeal 𝒪 := (IsLocalRing.mem_maximalIdeal a).2 hu
  rw [hmax, Ideal.mem_span_singleton] at this
  exact this

theorem v_eq_one_of_isUnit_mk (hF : IsAdicFrame π ϖ R) (r : R)
    (h : IsUnit (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)}) r)) :
    Valued.v (algebraMap R C r) = 1 := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : modPow π R 0)
  have h1 : Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)}) (r * s) = 1 := by
    rw [map_mul, ← hu, hs, Units.mul_inv]
  rw [← (Ideal.Quotient.mk _).map_one, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h1
  obtain ⟨t, ht⟩ := h1
  have hrs : r * s = 1 + algebraMap 𝒪 R π * t := by rw [pow_succ, pow_zero, one_mul] at ht; linear_combination ht
  have hv : Valued.v (algebraMap R C (r * s)) = 1 := by
    rw [hrs, map_add, map_one, map_mul, ← IsScalarTower.algebraMap_apply]
    apply Valuation.map_one_add_of_lt
    rw [map_mul]
    calc Valued.v (algebraMap 𝒪 C π) * Valued.v (algebraMap R C t) ≤ Valued.v (algebraMap 𝒪 C π) * 1 :=
          mul_le_mul' le_rfl (hF.v_algebraMap_le_one t)
      _ < 1 := by rw [mul_one]; exact hF.v_algebraMap_lt_one
  rw [map_mul, map_mul] at hv
  apply le_antisymm (hF.v_algebraMap_le_one r)
  by_contra hlt
  have : Valued.v (algebraMap R C r) * Valued.v (algebraMap R C s) < 1 :=
    mul_lt_one_of_lt_of_le (not_le.mp hlt) (hF.v_algebraMap_le_one s)
  rw [hv] at this
  exact lt_irrefl _ this

theorem not_exists_eq_smul_of_apply_eq_one (hπ : Irreducible π) (v : ↥(stdFullLattice (𝒪 := 𝒪) K).1) (i : Fin 2)
    (hi : (v : Fin 2 → K) i = 1) :
    ¬ ∃ w : ↥(stdFullLattice (𝒪 := 𝒪) K).1, (v : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K) := by
  rintro ⟨w, hw⟩
  have h := congrFun hw i
  rw [hi, Pi.smul_apply, smul_eq_mul] at h
  obtain ⟨y, hy⟩ := (mem_stdLattice 𝒪 K).1 w.2 i
  rw [← hy, ← map_mul, ← (algebraMap 𝒪 K).map_one] at h
  have h1 : (1 : 𝒪) = π * y := IsFractionRing.injective 𝒪 K h
  exact hπ.not_isUnit (isUnit_iff_exists_inv.2 ⟨y, h1.symm⟩)

theorem exists_eq_vec (v : ↥(stdFullLattice (𝒪 := 𝒪) K).1) :
    ∃ a b : 𝒪, v = ⟨vec (algebraMap 𝒪 K a) (algebraMap 𝒪 K b), vec_mem_stdLattice a b⟩ := by
  obtain ⟨a, ha⟩ := (mem_stdLattice 𝒪 K).1 v.2 0
  obtain ⟨b, hb⟩ := (mem_stdLattice 𝒪 K).1 v.2 1
  refine ⟨a, b, Subtype.ext ?_⟩
  show (v : Fin 2 → K) = vec (algebraMap 𝒪 K a) (algebraMap 𝒪 K b)
  rw [eq_vec (v : Fin 2 → K), ha, hb]

end FrameHelpers
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"

end CerednikDrinfeld.FormalOmega.T4VAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "FormalOmega.AdicPoint tree Omega.mem_stdEdgeTube_iff Omega.vertexTube Omega.edgeTube Omega.mem_vertexTube_iff Omega.mem_edgeTube_iff Omega.pmoebius Omega.upperHalfPlane Omega.pmoebius_mem_upperHalfPlane Omega.pmoebius_one Omega.pmoebius_mul FormalOmega.AdicPoint.toOmega_act FormalOmega.AdicPoint.toOmega_mem_upperHalfPlane"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt DeligneDatum.InVertexChart DeligneDatum.InEdgeChart modPow span_pow_succ_le modPowTransition AdicPoint stdFullLattice stdBasisVec coordToTensor AdicPoint.mem_stdLine_iff AdicPoint.act_pt AdicPoint.lineC AdicPoint.vecCons_toOmega_mem edgeFlip_ne_zero edgeFlip edgeFlip_mulVec pmoebius_edgeFlip coe_ofEq_apply coe_latticeMapEquiv_apply actBaseChange_tmul DeligneDatum.pullback rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum lineBaseChange AdicPoint.toOmega_act AdicPoint.toOmega_mem_upperHalfPlane"
namespace T4VAux
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

open TensorProduct CerednikDrinfeld.FormalOmega.T2aAux CerednikDrinfeld.FormalOmega.LevelAux

section Core

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}
  {C : Type} [Field C] [Algebra K C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]

theorem mem_affinoid_zero_iff (ϖ : PseudoUniformizer K C) (w : C) :
    w ∈ affinoid ϖ 0 ↔ Valued.v w ≤ 1 ∧
      ∀ a : K, Valued.v (algebraMap K C a) ≤ 1 → 1 ≤ Valued.v (w - algebraMap K C a) := by
  simp only [affinoid, Set.mem_setOf_eq, pow_zero]

theorem one_tmul_vec_mem_sup_iff (y : AdicPoint K π R) (c : modPow π R 0)
    (hc : lineCoord y 0 = Submodule.span _ {vec c 1}) (𝔭 : Ideal (modPow π R 0)) (a b : 𝒪) :
    (1 : modPow π R 0) ⊗ₜ[𝒪] (⟨vec (algebraMap 𝒪 K a) (algebraMap 𝒪 K b), vec_mem_stdLattice a b⟩ :
        ↥(stdFullLattice (𝒪 := 𝒪) K).1) ∈
      (y.pt 0).line (stdFullLattice K) ⊔ (𝔭 • ⊤ : Submodule (modPow π R 0) (latticeBaseChange 𝒪 K (modPow π R 0) (stdFullLattice K))) ↔
    algebraMap 𝒪 (modPow π R 0) a - algebraMap 𝒪 (modPow π R 0) b * c ∈ 𝔭 := by
  rw [mem_sup_smul_top_iff_map (coordEquiv (𝒪 := 𝒪) K (modPow π R 0)), coordEquiv_one_tmul_vec]
  change vec (algebraMap 𝒪 (modPow π R 0) a) (algebraMap 𝒪 (modPow π R 0) b) ∈ lineCoord y 0 ⊔ _ ↔ _
  rw [hc, vec_mem_span_vec_one_sup_iff]

theorem inVertexChart_std_iff (ϖ : PseudoUniformizer K C) (hF : IsAdicFrame π ϖ R) (y : AdicPoint K π R) :
    (y.pt 0).InVertexChart π (stdFullLattice K) ↔ y.toOmega C ∈ affinoid ϖ 0 := by
  classical
  have hπ := hF.irreducible
  haveI := isLocalRing_modPow hF 0
  have hmk : ∀ a : 𝒪, algebraMap 𝒪 (modPow π R 0) a =
      Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)}) (algebraMap 𝒪 R a) := fun a => by
    rw [IsScalarTower.algebraMap_apply 𝒪 R (modPow π R 0), Ideal.Quotient.algebraMap_eq]
  have hRC : ∀ a : 𝒪, algebraMap R C (algebraMap 𝒪 R a) = algebraMap K C (algebraMap 𝒪 K a) := fun a => by
    rw [← IsScalarTower.algebraMap_apply 𝒪 R C, IsScalarTower.algebraMap_apply 𝒪 K C]
  by_cases h0 : ∃ c, lineCoord y 0 = Submodule.span _ {vec c 1}
  ·
    choose c hc using typeII_all hF y h0
    have hcompat : ∀ n, modPowTransition π R n (c (n + 1)) = c n := by
      intro n
      have h' := lineCoord_eq_of_succ y n (c (n + 1)) 1 (hc (n + 1))
      rw [map_one, hc n] at h'
      exact (eq_of_span_vec_one_eq' h').symm
    obtain ⟨L, hL⟩ := exists_lift hF c hcompat
    have hstd : y.stdLine = Submodule.span R {vec L 1} :=
      stdLine_eq_span_II hF y L (fun n => by rw [hc n, hL n])
    have hlineC : y.lineC C = Submodule.span C {vec (algebraMap R C L) 1} := by
      rw [lineC_eq_of_stdLine_eq y _ hstd, algebraMap_vec, map_one]
    have hmemL : (![algebraMap R C L, 1] : Fin 2 → C) ∈ y.lineC C := by
      rw [hlineC, vecLit_eq_vec, mem_span_vec_one_iff']; simp
    have huniq : ∃! z : C, (![z, 1] : Fin 2 → C) ∈ y.lineC C := by
      refine ⟨algebraMap R C L, hmemL, fun z hz => ?_⟩
      rw [hlineC, vecLit_eq_vec, mem_span_vec_one_iff'] at hz
      simpa using hz
    have hz : y.toOmega C = algebraMap R C L := huniq.unique (AdicPoint.vecCons_toOmega_mem C y huniq) hmemL
    rw [hz, mem_affinoid_zero_iff]
    have hc0 : lineCoord y 0 = Submodule.span _ {vec (Ideal.Quotient.mk _ L) 1} := by rw [hc 0, hL 0]

    have crit : ∀ (𝔭 : Ideal (modPow π R 0)) (a b : 𝒪),
        (1 : modPow π R 0) ⊗ₜ[𝒪] (⟨vec (algebraMap 𝒪 K a) (algebraMap 𝒪 K b), vec_mem_stdLattice a b⟩ :
            ↥(stdFullLattice (𝒪 := 𝒪) K).1) ∈
          (y.pt 0).line (stdFullLattice K) ⊔ (𝔭 • ⊤ : Submodule (modPow π R 0) _) ↔
        Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)}) (algebraMap 𝒪 R a - algebraMap 𝒪 R b * L) ∈ 𝔭 := by
      intro 𝔭 a b
      rw [one_tmul_vec_mem_sup_iff y _ hc0 𝔭 a b, hmk, hmk, ← map_mul, ← map_sub]
    constructor
    ·
      intro hV
      refine ⟨hF.v_algebraMap_le_one L, fun t ht => ?_⟩
      obtain ⟨t₀, rfl⟩ := (hF.integers t).1 ht
      set vt : ↥(stdFullLattice (𝒪 := 𝒪) K).1 :=
        ⟨vec (algebraMap 𝒪 K t₀) (algebraMap 𝒪 K 1), vec_mem_stdLattice t₀ 1⟩ with hvt
      have hprim := not_exists_eq_smul_of_apply_eq_one hπ vt 1 (by simp [hvt])
      have h1 := hV (IsLocalRing.maximalIdeal _) (IsLocalRing.maximalIdeal.isMaximal _).isPrime vt hprim
      rw [hvt, crit] at h1
      have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)})
          (algebraMap 𝒪 R t₀ - algebraMap 𝒪 R 1 * L)) := by
        by_contra hu
        exact h1 ((IsLocalRing.mem_maximalIdeal _).2 hu)
      have hv1 := v_eq_one_of_isUnit_mk hF _ hunit
      rw [map_one, one_mul, map_sub, hRC] at hv1
      rw [← Valuation.map_neg, neg_sub, hv1]
    ·
      rintro ⟨-, hL0⟩ 𝔭 h𝔭 v hv hmem
      obtain ⟨a, b, rfl⟩ := exists_eq_vec v
      rw [crit] at hmem

      have hvab : Valued.v (algebraMap R C (algebraMap 𝒪 R a - algebraMap 𝒪 R b * L)) = 1 := by
        rw [map_sub, map_mul, hRC, hRC]
        by_cases hb : π ∣ b
        ·
          have ha : ¬ π ∣ a := by
            intro ha
            obtain ⟨a₁, rfl⟩ := ha
            obtain ⟨b₁, rfl⟩ := hb
            exact hv ⟨⟨vec (algebraMap 𝒪 K a₁) (algebraMap 𝒪 K b₁), vec_mem_stdLattice a₁ b₁⟩, by
              simp only [smul_vec, ← map_mul]⟩
          have hva : Valued.v (algebraMap K C (algebraMap 𝒪 K a)) = 1 := by
            rw [← IsScalarTower.algebraMap_apply 𝒪 K C]; exact v_algebraMap_unit_eq_one hF (isUnit_of_not_dvd hπ ha)
          have hvb : Valued.v (algebraMap K C (algebraMap 𝒪 K b) * algebraMap R C L) < 1 := by
            obtain ⟨b₁, rfl⟩ := hb
            rw [map_mul, ← IsScalarTower.algebraMap_apply 𝒪 K C, map_mul, map_mul]
            calc Valued.v (algebraMap 𝒪 C π) * Valued.v (algebraMap 𝒪 C b₁) * Valued.v (algebraMap R C L)
                ≤ Valued.v (algebraMap 𝒪 C π) * 1 * 1 :=
                  mul_le_mul' (mul_le_mul' le_rfl (v_algebraMap_int_le_one hF b₁)) (hF.v_algebraMap_le_one L)
              _ < 1 := by rw [mul_one, mul_one]; exact hF.v_algebraMap_lt_one
          rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left, hva]
          rw [Valuation.map_neg, hva]; exact hvb
        · have hbu := isUnit_of_not_dvd hπ hb
          obtain ⟨u, hu⟩ := hbu
          have hvb : Valued.v (algebraMap K C (algebraMap 𝒪 K b)) = 1 := by
            rw [← IsScalarTower.algebraMap_apply 𝒪 K C, ← hu]; exact v_algebraMap_unit_eq_one hF u.isUnit
          have ht := hL0 (algebraMap 𝒪 K (↑u⁻¹ * a)) (by
            rw [← IsScalarTower.algebraMap_apply 𝒪 K C]; exact v_algebraMap_int_le_one hF _)
          have hfac : algebraMap K C (algebraMap 𝒪 K a) - algebraMap K C (algebraMap 𝒪 K b) * algebraMap R C L =
              -(algebraMap K C (algebraMap 𝒪 K b)) * (algebraMap R C L - algebraMap K C (algebraMap 𝒪 K (↑u⁻¹ * a))) := by
            rw [← hu, map_mul, map_mul, ← IsScalarTower.algebraMap_apply 𝒪 K C, ← IsScalarTower.algebraMap_apply 𝒪 K C,
              ← IsScalarTower.algebraMap_apply 𝒪 K C]
            have : algebraMap 𝒪 C (u : 𝒪) * algebraMap 𝒪 C (↑u⁻¹ : 𝒪) = 1 := by
              rw [← map_mul, Units.mul_inv, map_one]
            linear_combination (-(algebraMap 𝒪 C a)) * this
          rw [hfac, map_mul, Valuation.map_neg, hvb, one_mul]
          exact le_antisymm
            (by
              have := Valuation.map_sub Valued.v (algebraMap R C L) (algebraMap K C (algebraMap 𝒪 K (↑u⁻¹ * a)))
              refine this.trans (max_le (hF.v_algebraMap_le_one L) ?_)
              rw [← IsScalarTower.algebraMap_apply 𝒪 K C]; exact v_algebraMap_int_le_one hF _)
            ht
      have hunitR : IsUnit (algebraMap 𝒪 R a - algebraMap 𝒪 R b * L) := (isUnit_iff_v_eq_one hF _).2 hvab
      have hunit := hunitR.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)}))
      exact h𝔭.ne_top (Ideal.eq_top_of_isUnit_mem 𝔭 hmem hunit)
  ·
    choose c hc using typeI_all hF y h0
    have hcompat : ∀ n, modPowTransition π R n (c (n + 1)) = c n := by
      intro n
      have h' := lineCoord_eq_of_succ y n 1 (c (n + 1)) (hc (n + 1))
      rw [map_one, hc n] at h'
      exact (eq_of_span_vec_one_eq h').symm
    obtain ⟨L, hL⟩ := exists_lift hF c hcompat
    have hstd : y.stdLine = Submodule.span R {vec 1 L} :=
      stdLine_eq_span_I hF y L (fun n => by rw [hc n, hL n])
    have hL0 : L ≠ 0 := by
      intro hL0
      apply not_forall_one_tmul_single_mem hF y
      intro n
      apply one_tmul_single_mem_of_lineCoord y n
      rw [hc n, ← hL n, hL0, map_zero]
    have hLC : algebraMap R C L ≠ 0 := fun h => hL0 (hF.injective (by rw [h, map_zero]))
    have hlineC : y.lineC C = Submodule.span C {vec 1 (algebraMap R C L)} := by
      rw [lineC_eq_of_stdLine_eq y _ hstd, algebraMap_vec, map_one]
    have hmemL : (![(algebraMap R C L)⁻¹, 1] : Fin 2 → C) ∈ y.lineC C := by
      rw [hlineC, vecLit_eq_vec, mem_span_vec_one_iff]; simp [mul_inv_cancel₀ hLC]
    have huniq : ∃! z : C, (![z, 1] : Fin 2 → C) ∈ y.lineC C := by
      refine ⟨(algebraMap R C L)⁻¹, hmemL, fun z hz => ?_⟩
      rw [hlineC, vecLit_eq_vec, mem_span_vec_one_iff] at hz
      simp only [vec_apply_one, vec_apply_zero] at hz
      calc z = (algebraMap R C L)⁻¹ * (algebraMap R C L * z) := by rw [← mul_assoc, inv_mul_cancel₀ hLC, one_mul]
        _ = (algebraMap R C L)⁻¹ := by rw [← hz, mul_one]
    have hz : y.toOmega C = (algebraMap R C L)⁻¹ := huniq.unique (AdicPoint.vecCons_toOmega_mem C y huniq) hmemL

    have hLnu : ¬ IsUnit (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)}) L) := by
      intro hu
      apply h0
      refine ⟨↑hu.unit⁻¹, ?_⟩
      rw [hc 0, ← hL 0, ← span_vec_unit' hu.unit, IsUnit.unit_spec]
    have hvL : Valued.v (algebraMap R C L) < 1 := by
      refine lt_of_le_of_ne (hF.v_algebraMap_le_one L) fun h => hLnu ?_
      exact ((isUnit_iff_v_eq_one hF L).2 h).map _
    refine iff_of_false (fun hV => ?_) (fun hR => ?_)
    ·
      set e₀ : ↥(stdFullLattice (𝒪 := 𝒪) K).1 := stdBasisVec K 0 with he₀
      have hprim := not_exists_eq_smul_of_apply_eq_one hπ e₀ 0 (by simp [he₀, stdBasisVec])
      have h1 := hV (IsLocalRing.maximalIdeal _) (IsLocalRing.maximalIdeal.isMaximal _).isPrime e₀ hprim
      apply h1
      rw [mem_sup_smul_top_iff_map (coordEquiv (𝒪 := 𝒪) K (modPow π R 0)), he₀, coordEquiv_tmul]
      change Pi.single 0 1 ∈ lineCoord y 0 ⊔ _
      rw [← vec_one_zero_eq_single 0, hc 0]
      exact vec_one_zero_mem_span_sup _ _ ((IsLocalRing.mem_maximalIdeal _).2 (by rw [← hL 0]; exact hLnu))
    · rw [hz, mem_affinoid_zero_iff] at hR
      have := hR.1
      rw [map_inv₀, inv_le_one₀ (by rwa [Valuation.pos_iff])] at this
      exact not_lt.2 this hvL

end Core
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"

end CerednikDrinfeld.FormalOmega.T4VAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "FormalOmega.AdicPoint tree Omega.mem_stdEdgeTube_iff Omega.vertexTube Omega.edgeTube Omega.mem_vertexTube_iff Omega.mem_edgeTube_iff Omega.pmoebius Omega.upperHalfPlane Omega.pmoebius_mem_upperHalfPlane Omega.pmoebius_one Omega.pmoebius_mul FormalOmega.AdicPoint.toOmega_act FormalOmega.AdicPoint.toOmega_mem_upperHalfPlane"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt DeligneDatum.InVertexChart DeligneDatum.InEdgeChart modPow span_pow_succ_le modPowTransition AdicPoint stdFullLattice stdBasisVec coordToTensor AdicPoint.mem_stdLine_iff AdicPoint.act_pt AdicPoint.lineC AdicPoint.vecCons_toOmega_mem edgeFlip_ne_zero edgeFlip edgeFlip_mulVec pmoebius_edgeFlip coe_ofEq_apply coe_latticeMapEquiv_apply actBaseChange_tmul DeligneDatum.pullback rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum lineBaseChange AdicPoint.toOmega_act AdicPoint.toOmega_mem_upperHalfPlane"
namespace T4EAux
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

open TensorProduct CerednikDrinfeld.FormalOmega.T2aAux CerednikDrinfeld.FormalOmega.LevelAux CerednikDrinfeld.FormalOmega.T4VAux

open scoped Matrix

section Transport

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem forall_not_mem_pullback_iff (h : GL (Fin 2) K) (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B)
    (M : FullLattice 𝒪 K) (P : ↥M.1 → Prop) (P' : ↥(FullLattice.act h M).1 → Prop)
    (hPP' : ∀ u : ↥M.1, P u ↔ P' (latticeMapEquiv h M.1 u)) :
    (∀ u : ↥M.1, P u → (1 : B) ⊗ₜ[𝒪] u ∉ (DeligneDatum.pullback π B h d).line M ⊔
        (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) ↔
    (∀ v : ↥(FullLattice.act h M).1, P' v → (1 : B) ⊗ₜ[𝒪] v ∉ d.line (FullLattice.act h M) ⊔
        (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (FullLattice.act h M)))) := by
  constructor
  · intro H v hv
    obtain ⟨u, rfl⟩ := (latticeMapEquiv h M.1).surjective v
    have h1 := H u ((hPP' u).2 hv)
    intro hmem
    apply h1
    show (1 : B) ⊗ₜ[𝒪] u ∈ (d.line (FullLattice.act h M)).comap (actBaseChange B h M).toLinearMap ⊔ (𝔭 • ⊤)
    rw [mem_comap_sup_smul_top_iff, actBaseChange_tmul]
    exact hmem
  · intro H u hu hmem
    have h1 := H (latticeMapEquiv h M.1 u) ((hPP' u).1 hu)
    apply h1
    change (1 : B) ⊗ₜ[𝒪] u ∈ (d.line (FullLattice.act h M)).comap (actBaseChange B h M).toLinearMap ⊔ (𝔭 • ⊤) at hmem
    rw [mem_comap_sup_smul_top_iff, actBaseChange_tmul] at hmem
    exact hmem

end Transport
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"

section VecI

variable {B : Type} [CommRing B]

theorem vec_mem_span_one_vec_sup_iff (c a b : B) (I : Ideal B) :
    vec a b ∈ Submodule.span B {vec 1 c} ⊔ (I • ⊤ : Submodule B (Fin 2 → B)) ↔ b - a * c ∈ I := by
  constructor
  · intro h
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [mem_smul_top_pi_iff] at hz
    have h0 := congrFun hyz 0
    have h1 := congrFun hyz 1
    simp only [Pi.add_apply, smul_vec, vec_apply_zero, vec_apply_one, mul_one] at h0 h1
    have : b - a * c = z 1 - z 0 * c := by rw [← h0, ← h1]; ring
    rw [this]
    exact I.sub_mem hz.2 (I.mul_mem_right _ hz.1)
  · intro h
    have : vec a b = a • vec 1 c + vec 0 (b - a * c) := by
      rw [smul_vec, vec_add_vec]; congr 1 <;> ring
    rw [this]
    exact Submodule.mem_sup.2 ⟨a • vec 1 c, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),
      vec 0 (b - a * c), (mem_smul_top_pi_iff I _).2 ⟨by simp, by simpa using h⟩, rfl⟩

end VecI
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"

section SigmaLattice

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}
  {C : Type} [Field C] [Algebra K C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]
  {ϖ : PseudoUniformizer K C}

theorem algebraMap_pi_eq (hF : IsAdicFrame π ϖ R) : algebraMap 𝒪 K π = ϖ.ϖ := by
  apply (algebraMap K C).injective
  rw [← IsScalarTower.algebraMap_apply 𝒪 K C, hF.unif]

theorem edgeFlip_mulVec_vec (hF : IsAdicFrame π ϖ R) (a b : K) :
    ((edgeFlip K ϖ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ vec a b = vec (algebraMap 𝒪 K π * a) b := by
  rw [edgeFlip_mulVec, algebraMap_pi_eq hF, vecLit_eq_vec, vec_apply_zero, vec_apply_one]

theorem vec_mem_latticeMap_edgeFlip_iff (hF : IsAdicFrame π ϖ R) (a b : 𝒪) :
    (vec (algebraMap 𝒪 K a) (algebraMap 𝒪 K b) : Fin 2 → K) ∈ latticeMap (edgeFlip K ϖ) (stdLattice 𝒪 K) ↔ π ∣ a := by
  have hπ := hF.irreducible
  rw [mem_latticeMap]
  constructor
  · rintro ⟨w, hw, hwv⟩
    obtain ⟨w₀, hw₀⟩ := (mem_stdLattice 𝒪 K).1 hw 0
    rw [eq_vec w, edgeFlip_mulVec_vec hF, vec_eq_vec_iff, ← hw₀, ← map_mul] at hwv
    exact ⟨w₀, (IsFractionRing.injective 𝒪 K hwv.1).symm⟩
  · rintro ⟨a₁, rfl⟩
    refine ⟨vec (algebraMap 𝒪 K a₁) (algebraMap 𝒪 K b), vec_mem_stdLattice a₁ b, ?_⟩
    rw [edgeFlip_mulVec_vec hF, ← map_mul]

theorem exists_edgeFlip_mulVec_eq_smul_iff (hF : IsAdicFrame π ϖ R) (a b : 𝒪) :
    (∃ w : ↥(stdFullLattice (𝒪 := 𝒪) K).1,
        ((edgeFlip K ϖ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (vec (algebraMap 𝒪 K a) (algebraMap 𝒪 K b)) =
          (algebraMap 𝒪 K π) • (w : Fin 2 → K)) ↔ π ∣ b := by
  rw [edgeFlip_mulVec_vec hF]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨w₁, hw₁⟩ := (mem_stdLattice 𝒪 K).1 w.2 1
    have h1 := congrFun hw 1
    rw [vec_apply_one, Pi.smul_apply, smul_eq_mul, ← hw₁, ← map_mul] at h1
    exact ⟨w₁, IsFractionRing.injective 𝒪 K h1⟩
  · rintro ⟨b₁, rfl⟩
    refine ⟨⟨vec (algebraMap 𝒪 K a) (algebraMap 𝒪 K b₁), vec_mem_stdLattice a b₁⟩, ?_⟩
    show vec (algebraMap 𝒪 K π * algebraMap 𝒪 K a) (algebraMap 𝒪 K (π * b₁)) =
      algebraMap 𝒪 K π • vec (algebraMap 𝒪 K a) (algebraMap 𝒪 K b₁)
    rw [smul_vec, map_mul]

theorem latticeMap_edgeFlip_le (hF : IsAdicFrame π ϖ R) :
    latticeMap (edgeFlip K ϖ) (stdLattice 𝒪 K) ≤ stdLattice 𝒪 K := by
  intro v hv
  rw [mem_latticeMap] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  obtain ⟨w₀, hw₀⟩ := (mem_stdLattice 𝒪 K).1 hw 0
  obtain ⟨w₁, hw₁⟩ := (mem_stdLattice 𝒪 K).1 hw 1
  rw [eq_vec w, edgeFlip_mulVec_vec hF, ← hw₀, ← hw₁, ← map_mul]
  exact vec_mem_stdLattice _ _

theorem smul_mem_latticeMap_edgeFlip (hF : IsAdicFrame π ϖ R) {u : Fin 2 → K} (hu : u ∈ stdLattice 𝒪 K) :
    (algebraMap 𝒪 K π) • u ∈ latticeMap (edgeFlip K ϖ) (stdLattice 𝒪 K) := by
  obtain ⟨u₀, hu₀⟩ := (mem_stdLattice 𝒪 K).1 hu 0
  obtain ⟨u₁, hu₁⟩ := (mem_stdLattice 𝒪 K).1 hu 1
  rw [eq_vec u, ← hu₀, ← hu₁, smul_vec, ← map_mul, ← map_mul, vec_mem_latticeMap_edgeFlip_iff hF]
  exact dvd_mul_right π u₀

end SigmaLattice
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"

end CerednikDrinfeld.FormalOmega.T4EAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "FormalOmega.AdicPoint tree Omega.mem_stdEdgeTube_iff Omega.vertexTube Omega.edgeTube Omega.mem_vertexTube_iff Omega.mem_edgeTube_iff Omega.pmoebius Omega.upperHalfPlane Omega.pmoebius_mem_upperHalfPlane Omega.pmoebius_one Omega.pmoebius_mul FormalOmega.AdicPoint.toOmega_act FormalOmega.AdicPoint.toOmega_mem_upperHalfPlane"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt DeligneDatum.InVertexChart DeligneDatum.InEdgeChart modPow span_pow_succ_le modPowTransition AdicPoint stdFullLattice stdBasisVec coordToTensor AdicPoint.mem_stdLine_iff AdicPoint.act_pt AdicPoint.lineC AdicPoint.vecCons_toOmega_mem edgeFlip_ne_zero edgeFlip edgeFlip_mulVec pmoebius_edgeFlip coe_ofEq_apply coe_latticeMapEquiv_apply actBaseChange_tmul DeligneDatum.pullback rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum lineBaseChange AdicPoint.toOmega_act AdicPoint.toOmega_mem_upperHalfPlane"
namespace T4EAux
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

open TensorProduct CerednikDrinfeld.FormalOmega.T2aAux CerednikDrinfeld.FormalOmega.LevelAux CerednikDrinfeld.FormalOmega.T4VAux

open scoped Matrix

section Cores

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}
  {C : Type} [Field C] [Algebra K C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]

theorem typeData (ϖ : PseudoUniformizer K C) (hF : IsAdicFrame π ϖ R) (y : AdicPoint K π R) :
    (∃ L : R, y.toOmega C = algebraMap R C L ∧
        lineCoord y 0 = Submodule.span _ {vec (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)}) L) 1}) ∨
    (∃ L : R, y.toOmega C = (algebraMap R C L)⁻¹ ∧ Valued.v (algebraMap R C L) < 1 ∧ algebraMap R C L ≠ 0 ∧
        lineCoord y 0 = Submodule.span _ {vec 1 (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)}) L)} ∧
        ¬ IsUnit (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)}) L)) := by
  classical
  by_cases h0 : ∃ c, lineCoord y 0 = Submodule.span _ {vec c 1}
  · left
    choose c hc using typeII_all hF y h0
    have hcompat : ∀ n, modPowTransition π R n (c (n + 1)) = c n := by
      intro n
      have h' := lineCoord_eq_of_succ y n (c (n + 1)) 1 (hc (n + 1))
      rw [map_one, hc n] at h'
      exact (eq_of_span_vec_one_eq' h').symm
    obtain ⟨L, hL⟩ := exists_lift hF c hcompat
    have hstd : y.stdLine = Submodule.span R {vec L 1} :=
      stdLine_eq_span_II hF y L (fun n => by rw [hc n, hL n])
    have hlineC : y.lineC C = Submodule.span C {vec (algebraMap R C L) 1} := by
      rw [lineC_eq_of_stdLine_eq y _ hstd, algebraMap_vec, map_one]
    have hmemL : (![algebraMap R C L, 1] : Fin 2 → C) ∈ y.lineC C := by
      rw [hlineC, vecLit_eq_vec, mem_span_vec_one_iff']; simp
    have huniq : ∃! z : C, (![z, 1] : Fin 2 → C) ∈ y.lineC C := by
      refine ⟨algebraMap R C L, hmemL, fun z hz => ?_⟩
      rw [hlineC, vecLit_eq_vec, mem_span_vec_one_iff'] at hz
      simpa using hz
    have hz : y.toOmega C = algebraMap R C L := huniq.unique (AdicPoint.vecCons_toOmega_mem C y huniq) hmemL
    exact ⟨L, hz, by rw [hc 0, hL 0]⟩
  · right
    choose c hc using typeI_all hF y h0
    have hcompat : ∀ n, modPowTransition π R n (c (n + 1)) = c n := by
      intro n
      have h' := lineCoord_eq_of_succ y n 1 (c (n + 1)) (hc (n + 1))
      rw [map_one, hc n] at h'
      exact (eq_of_span_vec_one_eq h').symm
    obtain ⟨L, hL⟩ := exists_lift hF c hcompat
    have hstd : y.stdLine = Submodule.span R {vec 1 L} :=
      stdLine_eq_span_I hF y L (fun n => by rw [hc n, hL n])
    have hL0 : L ≠ 0 := by
      intro hL0
      apply not_forall_one_tmul_single_mem hF y
      intro n
      apply one_tmul_single_mem_of_lineCoord y n
      rw [hc n, ← hL n, hL0, map_zero]
    have hLC : algebraMap R C L ≠ 0 := fun h => hL0 (hF.injective (by rw [h, map_zero]))
    have hlineC : y.lineC C = Submodule.span C {vec 1 (algebraMap R C L)} := by
      rw [lineC_eq_of_stdLine_eq y _ hstd, algebraMap_vec, map_one]
    have hmemL : (![(algebraMap R C L)⁻¹, 1] : Fin 2 → C) ∈ y.lineC C := by
      rw [hlineC, vecLit_eq_vec, mem_span_vec_one_iff]; simp [mul_inv_cancel₀ hLC]
    have huniq : ∃! z : C, (![z, 1] : Fin 2 → C) ∈ y.lineC C := by
      refine ⟨(algebraMap R C L)⁻¹, hmemL, fun z hz => ?_⟩
      rw [hlineC, vecLit_eq_vec, mem_span_vec_one_iff] at hz
      simp only [vec_apply_one, vec_apply_zero] at hz
      calc z = (algebraMap R C L)⁻¹ * (algebraMap R C L * z) := by rw [← mul_assoc, inv_mul_cancel₀ hLC, one_mul]
        _ = (algebraMap R C L)⁻¹ := by rw [← hz, mul_one]
    have hz : y.toOmega C = (algebraMap R C L)⁻¹ := huniq.unique (AdicPoint.vecCons_toOmega_mem C y huniq) hmemL
    have hLnu : ¬ IsUnit (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)}) L) := by
      intro hu
      apply h0
      refine ⟨↑hu.unit⁻¹, ?_⟩
      rw [hc 0, ← hL 0, ← span_vec_unit' hu.unit, IsUnit.unit_spec]
    have hvL : Valued.v (algebraMap R C L) < 1 := by
      refine lt_of_le_of_ne (hF.v_algebraMap_le_one L) fun h => hLnu ?_
      exact ((isUnit_iff_v_eq_one hF L).2 h).map _
    exact ⟨L, hz, hvL, hLC, by rw [hc 0, hL 0], hLnu⟩

theorem one_tmul_vec_mem_sup_iff' (y : AdicPoint K π R) (c : modPow π R 0)
    (hc : lineCoord y 0 = Submodule.span _ {vec 1 c}) (𝔭 : Ideal (modPow π R 0)) (a b : 𝒪) :
    (1 : modPow π R 0) ⊗ₜ[𝒪] (⟨vec (algebraMap 𝒪 K a) (algebraMap 𝒪 K b), vec_mem_stdLattice a b⟩ :
        ↥(stdFullLattice (𝒪 := 𝒪) K).1) ∈
      (y.pt 0).line (stdFullLattice K) ⊔ (𝔭 • ⊤ : Submodule (modPow π R 0) (latticeBaseChange 𝒪 K (modPow π R 0) (stdFullLattice K))) ↔
    algebraMap 𝒪 (modPow π R 0) b - algebraMap 𝒪 (modPow π R 0) a * c ∈ 𝔭 := by
  rw [mem_sup_smul_top_iff_map (coordEquiv (𝒪 := 𝒪) K (modPow π R 0)), coordEquiv_one_tmul_vec]
  change vec (algebraMap 𝒪 (modPow π R 0) a) (algebraMap 𝒪 (modPow π R 0) b) ∈ lineCoord y 0 ⊔ _ ↔ _
  rw [hc, vec_mem_span_one_vec_sup_iff]

theorem v_eq_one_of_mem_affinoid_zero (ϖ : PseudoUniformizer K C) {w : C} (hw : w ∈ affinoid ϖ 0) : Valued.v w = 1 := by
  rw [mem_affinoid_zero_iff] at hw
  refine le_antisymm hw.1 ?_
  have := hw.2 0 (by rw [map_zero, map_zero]; exact zero_le_one)
  rwa [map_zero, sub_zero] at this

theorem coreP1 (ϖ : PseudoUniformizer K C) (hF : IsAdicFrame π ϖ R) (y : AdicPoint K π R) :
    (∀ 𝔭 : Ideal (modPow π R 0), 𝔭.IsPrime → ∀ u : ↥(stdFullLattice (𝒪 := 𝒪) K).1,
        (u : Fin 2 → K) ∉ latticeMap (edgeFlip K ϖ) (stdLattice 𝒪 K) →
        (1 : modPow π R 0) ⊗ₜ[𝒪] u ∉ (y.pt 0).line (stdFullLattice K) ⊔
          (𝔭 • ⊤ : Submodule (modPow π R 0) (latticeBaseChange 𝒪 K (modPow π R 0) (stdFullLattice K)))) ↔
    (Valued.v (y.toOmega C) < 1 ∨ y.toOmega C ∈ affinoid ϖ 0) := by
  classical
  have hπ := hF.irreducible
  haveI := isLocalRing_modPow hF 0
  have hmk : ∀ a : 𝒪, algebraMap 𝒪 (modPow π R 0) a =
      Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)}) (algebraMap 𝒪 R a) := fun a => by
    rw [IsScalarTower.algebraMap_apply 𝒪 R (modPow π R 0), Ideal.Quotient.algebraMap_eq]
  have hRC : ∀ a : 𝒪, algebraMap R C (algebraMap 𝒪 R a) = algebraMap K C (algebraMap 𝒪 K a) := fun a => by
    rw [← IsScalarTower.algebraMap_apply 𝒪 R C, IsScalarTower.algebraMap_apply 𝒪 K C]
  rcases typeData ϖ hF y with ⟨L, hz, hc0⟩ | ⟨L, hz, hvL, hLC, hc0, hLnu⟩
  ·
    rw [hz]
    have crit : ∀ (𝔭 : Ideal (modPow π R 0)) (a b : 𝒪),
        (1 : modPow π R 0) ⊗ₜ[𝒪] (⟨vec (algebraMap 𝒪 K a) (algebraMap 𝒪 K b), vec_mem_stdLattice a b⟩ :
            ↥(stdFullLattice (𝒪 := 𝒪) K).1) ∈
          (y.pt 0).line (stdFullLattice K) ⊔ (𝔭 • ⊤ : Submodule (modPow π R 0) _) ↔
        Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)}) (algebraMap 𝒪 R a - algebraMap 𝒪 R b * L) ∈ 𝔭 := by
      intro 𝔭 a b
      rw [one_tmul_vec_mem_sup_iff y _ hc0 𝔭 a b, hmk, hmk, ← map_mul, ← map_sub]
    constructor
    · intro hV
      by_cases hvL : Valued.v (algebraMap R C L) < 1
      · exact Or.inl hvL
      right
      have hvL1 : Valued.v (algebraMap R C L) = 1 := le_antisymm (hF.v_algebraMap_le_one L) (not_lt.1 hvL)
      rw [mem_affinoid_zero_iff]
      refine ⟨hF.v_algebraMap_le_one L, fun t ht => ?_⟩
      obtain ⟨t₀, rfl⟩ := (hF.integers t).1 ht
      by_cases ht₀ : π ∣ t₀
      ·
        obtain ⟨t₁, rfl⟩ := ht₀
        have hvt : Valued.v (algebraMap K C (algebraMap 𝒪 K (π * t₁))) < Valued.v (algebraMap R C L) := by
          rw [hvL1, ← IsScalarTower.algebraMap_apply 𝒪 K C, map_mul, map_mul]
          calc Valued.v (algebraMap 𝒪 C π) * Valued.v (algebraMap 𝒪 C t₁) ≤ Valued.v (algebraMap 𝒪 C π) * 1 :=
                mul_le_mul' le_rfl (v_algebraMap_int_le_one hF t₁)
            _ < 1 := by rw [mul_one]; exact hF.v_algebraMap_lt_one
        rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left, hvL1]
        rw [Valuation.map_neg]; exact hvt
      · set vt : ↥(stdFullLattice (𝒪 := 𝒪) K).1 :=
          ⟨vec (algebraMap 𝒪 K t₀) (algebraMap 𝒪 K 1), vec_mem_stdLattice t₀ 1⟩ with hvt
        have hside : (vt : Fin 2 → K) ∉ latticeMap (edgeFlip K ϖ) (stdLattice 𝒪 K) := by
          rw [hvt]; show vec (algebraMap 𝒪 K t₀) (algebraMap 𝒪 K 1) ∉ _
          rw [vec_mem_latticeMap_edgeFlip_iff hF]; exact ht₀
        have h1 := hV (IsLocalRing.maximalIdeal _) (IsLocalRing.maximalIdeal.isMaximal _).isPrime vt hside
        rw [hvt, crit] at h1
        have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)})
            (algebraMap 𝒪 R t₀ - algebraMap 𝒪 R 1 * L)) := by
          by_contra hu
          exact h1 ((IsLocalRing.mem_maximalIdeal _).2 hu)
        have hv1 := v_eq_one_of_isUnit_mk hF _ hunit
        rw [map_one, one_mul, map_sub, hRC] at hv1
        rw [← Valuation.map_neg, neg_sub, hv1]
    · intro hR 𝔭 h𝔭 u hu hmem
      obtain ⟨a, b, rfl⟩ := exists_eq_vec u
      have ha : ¬ π ∣ a := by
        intro ha; apply hu
        show vec (algebraMap 𝒪 K a) (algebraMap 𝒪 K b) ∈ _
        rw [vec_mem_latticeMap_edgeFlip_iff hF]; exact ha
      rw [crit] at hmem
      have hva : Valued.v (algebraMap K C (algebraMap 𝒪 K a)) = 1 := by
        rw [← IsScalarTower.algebraMap_apply 𝒪 K C]; exact v_algebraMap_unit_eq_one hF (isUnit_of_not_dvd hπ ha)
      have hvab : Valued.v (algebraMap R C (algebraMap 𝒪 R a - algebraMap 𝒪 R b * L)) = 1 := by
        rw [map_sub, map_mul, hRC, hRC]
        by_cases hsmall : Valued.v (algebraMap K C (algebraMap 𝒪 K b) * algebraMap R C L) < 1
        · rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left, hva]
          rw [Valuation.map_neg, hva]; exact hsmall
        ·
          have hb : ¬ π ∣ b := by
            rintro ⟨b₁, rfl⟩
            apply hsmall
            rw [map_mul, ← IsScalarTower.algebraMap_apply 𝒪 K C, map_mul, map_mul]
            calc Valued.v (algebraMap 𝒪 C π) * Valued.v (algebraMap 𝒪 C b₁) * Valued.v (algebraMap R C L)
                ≤ Valued.v (algebraMap 𝒪 C π) * 1 * 1 :=
                  mul_le_mul' (mul_le_mul' le_rfl (v_algebraMap_int_le_one hF b₁)) (hF.v_algebraMap_le_one L)
              _ < 1 := by rw [mul_one, mul_one]; exact hF.v_algebraMap_lt_one
          have hL0 : ∀ t : K, Valued.v (algebraMap K C t) ≤ 1 → 1 ≤ Valued.v (algebraMap R C L - algebraMap K C t) := by
            rcases hR with hlt | hmem0
            · exfalso; apply hsmall
              rw [map_mul, mul_comm]
              exact mul_lt_one_of_lt_of_le hlt (by rw [← IsScalarTower.algebraMap_apply 𝒪 K C]; exact v_algebraMap_int_le_one hF b)
            · exact ((mem_affinoid_zero_iff ϖ _).1 hmem0).2
          obtain ⟨u, hu'⟩ := isUnit_of_not_dvd hπ hb
          have hvb : Valued.v (algebraMap K C (algebraMap 𝒪 K b)) = 1 := by
            rw [← IsScalarTower.algebraMap_apply 𝒪 K C, ← hu']; exact v_algebraMap_unit_eq_one hF u.isUnit
          have ht := hL0 (algebraMap 𝒪 K (↑u⁻¹ * a)) (by
            rw [← IsScalarTower.algebraMap_apply 𝒪 K C]; exact v_algebraMap_int_le_one hF _)
          have hfac : algebraMap K C (algebraMap 𝒪 K a) - algebraMap K C (algebraMap 𝒪 K b) * algebraMap R C L =
              -(algebraMap K C (algebraMap 𝒪 K b)) * (algebraMap R C L - algebraMap K C (algebraMap 𝒪 K (↑u⁻¹ * a))) := by
            rw [← hu', map_mul, map_mul, ← IsScalarTower.algebraMap_apply 𝒪 K C, ← IsScalarTower.algebraMap_apply 𝒪 K C,
              ← IsScalarTower.algebraMap_apply 𝒪 K C]
            have : algebraMap 𝒪 C (u : 𝒪) * algebraMap 𝒪 C (↑u⁻¹ : 𝒪) = 1 := by
              rw [← map_mul, Units.mul_inv, map_one]
            linear_combination (-(algebraMap 𝒪 C a)) * this
          rw [hfac, map_mul, Valuation.map_neg, hvb, one_mul]
          exact le_antisymm
            (by
              have := Valuation.map_sub Valued.v (algebraMap R C L) (algebraMap K C (algebraMap 𝒪 K (↑u⁻¹ * a)))
              refine this.trans (max_le (hF.v_algebraMap_le_one L) ?_)
              rw [← IsScalarTower.algebraMap_apply 𝒪 K C]; exact v_algebraMap_int_le_one hF _)
            ht
      have hunitR : IsUnit (algebraMap 𝒪 R a - algebraMap 𝒪 R b * L) := (isUnit_iff_v_eq_one hF _).2 hvab
      exact h𝔭.ne_top (Ideal.eq_top_of_isUnit_mem 𝔭 hmem (hunitR.map _))
  ·
    rw [hz]
    refine iff_of_false (fun hV => ?_) (fun hR => ?_)
    · set e₀ : ↥(stdFullLattice (𝒪 := 𝒪) K).1 :=
        ⟨vec (algebraMap 𝒪 K 1) (algebraMap 𝒪 K 0), vec_mem_stdLattice 1 0⟩ with he₀
      have hside : (e₀ : Fin 2 → K) ∉ latticeMap (edgeFlip K ϖ) (stdLattice 𝒪 K) := by
        rw [he₀]; show vec (algebraMap 𝒪 K 1) (algebraMap 𝒪 K 0) ∉ _
        rw [vec_mem_latticeMap_edgeFlip_iff hF]; exact fun h => hπ.not_isUnit (isUnit_of_dvd_one h)
      have h1 := hV (IsLocalRing.maximalIdeal _) (IsLocalRing.maximalIdeal.isMaximal _).isPrime e₀ hside
      apply h1
      rw [he₀, one_tmul_vec_mem_sup_iff' y _ hc0, map_one, map_zero, one_mul, zero_sub]
      exact neg_mem ((IsLocalRing.mem_maximalIdeal _).2 hLnu)
    · rcases hR with hlt | hmem0
      · rw [map_inv₀] at hlt
        have : (1 : Γ₀) < Valued.v (algebraMap R C L) := by
          have h := hlt
          rwa [inv_lt_one₀ (by rwa [Valuation.pos_iff])] at h
        exact absurd (this.trans hvL) (lt_irrefl _)
      · have := ((mem_affinoid_zero_iff ϖ _).1 hmem0).1
        rw [map_inv₀, inv_le_one₀ (by rwa [Valuation.pos_iff])] at this
        exact not_lt.2 this hvL

theorem coreP2 (ϖ : PseudoUniformizer K C) (hF : IsAdicFrame π ϖ R) (y : AdicPoint K π R) :
    (∀ 𝔭 : Ideal (modPow π R 0), 𝔭.IsPrime → ∀ u : ↥(stdFullLattice (𝒪 := 𝒪) K).1,
        (¬ ∃ w : ↥(stdFullLattice (𝒪 := 𝒪) K).1,
            ((edgeFlip K ϖ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (u : Fin 2 → K) =
              (algebraMap 𝒪 K π) • (w : Fin 2 → K)) →
        (1 : modPow π R 0) ⊗ₜ[𝒪] u ∉ (y.pt 0).line (stdFullLattice K) ⊔
          (𝔭 • ⊤ : Submodule (modPow π R 0) (latticeBaseChange 𝒪 K (modPow π R 0) (stdFullLattice K)))) ↔
    (1 < Valued.v (y.toOmega C) ∨ y.toOmega C ∈ affinoid ϖ 0) := by
  classical
  have hπ := hF.irreducible
  haveI := isLocalRing_modPow hF 0
  have hmk : ∀ a : 𝒪, algebraMap 𝒪 (modPow π R 0) a =
      Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)}) (algebraMap 𝒪 R a) := fun a => by
    rw [IsScalarTower.algebraMap_apply 𝒪 R (modPow π R 0), Ideal.Quotient.algebraMap_eq]
  have hRC : ∀ a : 𝒪, algebraMap R C (algebraMap 𝒪 R a) = algebraMap K C (algebraMap 𝒪 K a) := fun a => by
    rw [← IsScalarTower.algebraMap_apply 𝒪 R C, IsScalarTower.algebraMap_apply 𝒪 K C]
  rcases typeData ϖ hF y with ⟨L, hz, hc0⟩ | ⟨L, hz, hvL, hLC, hc0, hLnu⟩
  ·
    rw [hz]
    have crit : ∀ (𝔭 : Ideal (modPow π R 0)) (a b : 𝒪),
        (1 : modPow π R 0) ⊗ₜ[𝒪] (⟨vec (algebraMap 𝒪 K a) (algebraMap 𝒪 K b), vec_mem_stdLattice a b⟩ :
            ↥(stdFullLattice (𝒪 := 𝒪) K).1) ∈
          (y.pt 0).line (stdFullLattice K) ⊔ (𝔭 • ⊤ : Submodule (modPow π R 0) _) ↔
        Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)}) (algebraMap 𝒪 R a - algebraMap 𝒪 R b * L) ∈ 𝔭 := by
      intro 𝔭 a b
      rw [one_tmul_vec_mem_sup_iff y _ hc0 𝔭 a b, hmk, hmk, ← map_mul, ← map_sub]
    have hnot1 : ¬ (1 < Valued.v (algebraMap R C L)) := not_lt.2 (hF.v_algebraMap_le_one L)
    constructor
    · intro hV
      right
      rw [mem_affinoid_zero_iff]
      refine ⟨hF.v_algebraMap_le_one L, fun t ht => ?_⟩
      obtain ⟨t₀, rfl⟩ := (hF.integers t).1 ht
      set vt : ↥(stdFullLattice (𝒪 := 𝒪) K).1 :=
        ⟨vec (algebraMap 𝒪 K t₀) (algebraMap 𝒪 K 1), vec_mem_stdLattice t₀ 1⟩ with hvt
      have hside : ¬ ∃ w : ↥(stdFullLattice (𝒪 := 𝒪) K).1,
          ((edgeFlip K ϖ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (vt : Fin 2 → K) =
            (algebraMap 𝒪 K π) • (w : Fin 2 → K) := by
        rw [hvt]
        show ¬ ∃ w : ↥(stdFullLattice (𝒪 := 𝒪) K).1, _ *ᵥ vec (algebraMap 𝒪 K t₀) (algebraMap 𝒪 K 1) = _
        rw [exists_edgeFlip_mulVec_eq_smul_iff hF]; exact fun h => hπ.not_isUnit (isUnit_of_dvd_one h)
      have h1 := hV (IsLocalRing.maximalIdeal _) (IsLocalRing.maximalIdeal.isMaximal _).isPrime vt hside
      rw [hvt, crit] at h1
      have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)})
          (algebraMap 𝒪 R t₀ - algebraMap 𝒪 R 1 * L)) := by
        by_contra hu
        exact h1 ((IsLocalRing.mem_maximalIdeal _).2 hu)
      have hv1 := v_eq_one_of_isUnit_mk hF _ hunit
      rw [map_one, one_mul, map_sub, hRC] at hv1
      rw [← Valuation.map_neg, neg_sub, hv1]
    · intro hR 𝔭 h𝔭 u hu hmem
      have hL0 : ∀ t : K, Valued.v (algebraMap K C t) ≤ 1 → 1 ≤ Valued.v (algebraMap R C L - algebraMap K C t) := by
        rcases hR with hlt | hmem0
        · exact absurd hlt hnot1
        · exact ((mem_affinoid_zero_iff ϖ _).1 hmem0).2
      obtain ⟨a, b, rfl⟩ := exists_eq_vec u
      have hb : ¬ π ∣ b := by
        intro hb; apply hu
        show ∃ w : ↥(stdFullLattice (𝒪 := 𝒪) K).1, _ *ᵥ vec (algebraMap 𝒪 K a) (algebraMap 𝒪 K b) = _
        rw [exists_edgeFlip_mulVec_eq_smul_iff hF]; exact hb
      rw [crit] at hmem
      obtain ⟨u', hu'⟩ := isUnit_of_not_dvd hπ hb
      have hvb : Valued.v (algebraMap K C (algebraMap 𝒪 K b)) = 1 := by
        rw [← IsScalarTower.algebraMap_apply 𝒪 K C, ← hu']; exact v_algebraMap_unit_eq_one hF u'.isUnit
      have ht := hL0 (algebraMap 𝒪 K (↑u'⁻¹ * a)) (by
        rw [← IsScalarTower.algebraMap_apply 𝒪 K C]; exact v_algebraMap_int_le_one hF _)
      have hvab : Valued.v (algebraMap R C (algebraMap 𝒪 R a - algebraMap 𝒪 R b * L)) = 1 := by
        rw [map_sub, map_mul, hRC, hRC]
        have hfac : algebraMap K C (algebraMap 𝒪 K a) - algebraMap K C (algebraMap 𝒪 K b) * algebraMap R C L =
            -(algebraMap K C (algebraMap 𝒪 K b)) * (algebraMap R C L - algebraMap K C (algebraMap 𝒪 K (↑u'⁻¹ * a))) := by
          rw [← hu', map_mul, map_mul, ← IsScalarTower.algebraMap_apply 𝒪 K C, ← IsScalarTower.algebraMap_apply 𝒪 K C,
            ← IsScalarTower.algebraMap_apply 𝒪 K C]
          have : algebraMap 𝒪 C (u' : 𝒪) * algebraMap 𝒪 C (↑u'⁻¹ : 𝒪) = 1 := by
            rw [← map_mul, Units.mul_inv, map_one]
          linear_combination (-(algebraMap 𝒪 C a)) * this
        rw [hfac, map_mul, Valuation.map_neg, hvb, one_mul]
        exact le_antisymm
          (by
            have := Valuation.map_sub Valued.v (algebraMap R C L) (algebraMap K C (algebraMap 𝒪 K (↑u'⁻¹ * a)))
            refine this.trans (max_le (hF.v_algebraMap_le_one L) ?_)
            rw [← IsScalarTower.algebraMap_apply 𝒪 K C]; exact v_algebraMap_int_le_one hF _)
          ht
      have hunitR : IsUnit (algebraMap 𝒪 R a - algebraMap 𝒪 R b * L) := (isUnit_iff_v_eq_one hF _).2 hvab
      exact h𝔭.ne_top (Ideal.eq_top_of_isUnit_mem 𝔭 hmem (hunitR.map _))
  ·
    rw [hz]
    refine iff_of_true ?_ (Or.inl ?_)
    · intro 𝔭 h𝔭 u hu hmem
      obtain ⟨a, b, rfl⟩ := exists_eq_vec u
      have hb : ¬ π ∣ b := by
        intro hb; apply hu
        show ∃ w : ↥(stdFullLattice (𝒪 := 𝒪) K).1, _ *ᵥ vec (algebraMap 𝒪 K a) (algebraMap 𝒪 K b) = _
        rw [exists_edgeFlip_mulVec_eq_smul_iff hF]; exact hb
      rw [one_tmul_vec_mem_sup_iff' y _ hc0, hmk, hmk] at hmem

      have hbu : IsUnit (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)}) (algebraMap 𝒪 R b)) :=
        ((isUnit_of_not_dvd hπ hb).map (algebraMap 𝒪 R)).map _
      have hm : Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)}) (algebraMap 𝒪 R a) *
          Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)}) L ∈ IsLocalRing.maximalIdeal (modPow π R 0) :=
        Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 hLnu)
      have hdiff : IsUnit (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)}) (algebraMap 𝒪 R b) -
          Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)}) (algebraMap 𝒪 R a) *
            Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)}) L) := by
        by_contra hnu
        have h1 := (IsLocalRing.mem_maximalIdeal _).2 hnu
        have h2 : Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)}) (algebraMap 𝒪 R b) ∈
            IsLocalRing.maximalIdeal (modPow π R 0) := by
          have := Ideal.add_mem _ h1 hm
          rwa [sub_add_cancel] at this
        exact (IsLocalRing.mem_maximalIdeal _).1 h2 hbu
      exact h𝔭.ne_top (Ideal.eq_top_of_isUnit_mem 𝔭 hmem hdiff)
    · rw [map_inv₀, one_lt_inv₀ (by rwa [Valuation.pos_iff])]
      exact hvL

end Cores
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"

end CerednikDrinfeld.FormalOmega.T4EAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "FormalOmega.AdicPoint tree Omega.mem_stdEdgeTube_iff Omega.vertexTube Omega.edgeTube Omega.mem_vertexTube_iff Omega.mem_edgeTube_iff Omega.pmoebius Omega.upperHalfPlane Omega.pmoebius_mem_upperHalfPlane Omega.pmoebius_one Omega.pmoebius_mul FormalOmega.AdicPoint.toOmega_act FormalOmega.AdicPoint.toOmega_mem_upperHalfPlane"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt DeligneDatum.InVertexChart DeligneDatum.InEdgeChart modPow span_pow_succ_le modPowTransition AdicPoint stdFullLattice stdBasisVec coordToTensor AdicPoint.mem_stdLine_iff AdicPoint.act_pt AdicPoint.lineC AdicPoint.vecCons_toOmega_mem edgeFlip_ne_zero edgeFlip edgeFlip_mulVec pmoebius_edgeFlip coe_ofEq_apply coe_latticeMapEquiv_apply actBaseChange_tmul DeligneDatum.pullback rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum lineBaseChange AdicPoint.toOmega_act AdicPoint.toOmega_mem_upperHalfPlane"
namespace T4EAux
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

open TensorProduct CerednikDrinfeld.FormalOmega.T2aAux CerednikDrinfeld.FormalOmega.LevelAux CerednikDrinfeld.FormalOmega.T4VAux

open scoped Matrix

section Assembly

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}
  {C : Type} [Field C] [Algebra K C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]

theorem mulVec_mem_latticeMap_iff (g : GL (Fin 2) K) (L : Submodule 𝒪 (Fin 2 → K)) (u : Fin 2 → K) :
    (g : Matrix (Fin 2) (Fin 2) K) *ᵥ u ∈ latticeMap g L ↔ u ∈ L := by
  rw [mem_latticeMap]
  constructor
  · rintro ⟨w, hw, hwu⟩
    have h := congrArg (fun x => Matrix.mulVec ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) x) hwu
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h
    rwa [← h]
  · intro hu; exact ⟨u, hu, rfl⟩

theorem pmoebius_edgeFlip_inv (ϖ : PseudoUniformizer K C) {w : C} (hw : w ∈ Omega.upperHalfPlane K C) :
    Omega.pmoebius K (Matrix.ProjGenLinGroup.mk (edgeFlip K ϖ))⁻¹ w = (algebraMap K C ϖ.ϖ)⁻¹ * w := by
  have hϖ : algebraMap K C ϖ.ϖ ≠ 0 := (map_ne_zero _).2 (edgeFlip_ne_zero K ϖ)
  have h := pmoebius_edgeFlip K ϖ (Omega.pmoebius K (Matrix.ProjGenLinGroup.mk (edgeFlip K ϖ))⁻¹ w)
  rw [← Omega.pmoebius_mul K hw, mul_inv_cancel, Omega.pmoebius_one] at h
  rw [eq_inv_mul_iff_mul_eq₀ hϖ]
  exact h.symm

theorem inv_mul_le_one_iff {a b : Γ₀} (ha : a ≠ 0) : a⁻¹ * b ≤ 1 ↔ b ≤ a := by
  constructor
  · intro h
    calc b = a * (a⁻¹ * b) := by rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
      _ ≤ a * 1 := mul_le_mul' le_rfl h
      _ = a := mul_one a
  · intro h
    calc a⁻¹ * b ≤ a⁻¹ * a := mul_le_mul' le_rfl h
      _ = 1 := inv_mul_cancel₀ ha

end Assembly
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"

end CerednikDrinfeld.FormalOmega.T4EAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.CerednikDrinfeld.FormalOmega.T2aAux"

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪}
    {C : Type} [Field C] [Algebra K C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]
    (ϖ : PseudoUniformizer K C) (hF : IsAdicFrame π ϖ R) (g : GL (Fin 2) K) (x : AdicPoint K π R) :
    (x.pt 0).InEdgeChart π (FullLattice.act (g * edgeFlip K ϖ) (stdFullLattice K)) (FullLattice.act g (stdFullLattice K)) ↔
      x.toOmega C ∈ Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪ Omega.edgeTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪
        Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g * edgeFlip K ϖ)) := by
  classical
  have hπ := hF.irreducible
  have hzΩ : x.toOmega C ∈ Omega.upperHalfPlane K C :=
    CerednikDrinfeld.FormalOmega.AdicPoint.toOmega_mem_upperHalfPlane ϖ hF x
  have hϖ0 : Valued.v (algebraMap K C ϖ.ϖ) ≠ 0 := ne_of_gt ϖ.pos

  set w : C := Omega.pmoebius K (Matrix.ProjGenLinGroup.mk g)⁻¹ (x.toOmega C) with hw
  have hwΩ : w ∈ Omega.upperHalfPlane K C := Omega.pmoebius_mem_upperHalfPlane K hzΩ _
  have hz1 : (x.act g⁻¹).toOmega C = w := by
    rw [CerednikDrinfeld.FormalOmega.AdicPoint.toOmega_act ϖ hF g⁻¹ x, map_inv]
  have hσw : Omega.pmoebius K (Matrix.ProjGenLinGroup.mk (g * edgeFlip K ϖ))⁻¹ (x.toOmega C) =
      (algebraMap K C ϖ.ϖ)⁻¹ * w := by
    rw [map_mul, mul_inv_rev, Omega.pmoebius_mul K hzΩ, ← hw]
    exact CerednikDrinfeld.FormalOmega.T4EAux.pmoebius_edgeFlip_inv ϖ hwΩ
  have hz2 : (x.act (g * edgeFlip K ϖ)⁻¹).toOmega C = (algebraMap K C ϖ.ϖ)⁻¹ * w := by
    rw [CerednikDrinfeld.FormalOmega.AdicPoint.toOmega_act ϖ hF (g * edgeFlip K ϖ)⁻¹ x, map_inv, hσw]

  have P1 := CerednikDrinfeld.FormalOmega.T4EAux.coreP1 ϖ hF (x.act g⁻¹)
  have P2 := CerednikDrinfeld.FormalOmega.T4EAux.coreP2 ϖ hF (x.act (g * edgeFlip K ϖ)⁻¹)
  rw [hz1, AdicPoint.act_pt, inv_inv] at P1
  rw [hz2, AdicPoint.act_pt, inv_inv] at P2

  have T1 : ∀ 𝔭 : Ideal (modPow π R 0),
      (∀ v : ↥(FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1,
          (v : Fin 2 → K) ∉ (FullLattice.act (g * edgeFlip K ϖ) (stdFullLattice (𝒪 := 𝒪) K)).1 →
          (1 : modPow π R 0) ⊗ₜ[𝒪] v ∉ (x.pt 0).line (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)) ⊔
            (𝔭 • ⊤ : Submodule (modPow π R 0) (latticeBaseChange 𝒪 K (modPow π R 0) (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K))))) ↔
      (∀ u : ↥(stdFullLattice (𝒪 := 𝒪) K).1,
          (u : Fin 2 → K) ∉ latticeMap (edgeFlip K ϖ) (stdLattice 𝒪 K) →
          (1 : modPow π R 0) ⊗ₜ[𝒪] u ∉ (DeligneDatum.pullback π (modPow π R 0) g (x.pt 0)).line (stdFullLattice (𝒪 := 𝒪) K) ⊔
            (𝔭 • ⊤ : Submodule (modPow π R 0) (latticeBaseChange 𝒪 K (modPow π R 0) (stdFullLattice (𝒪 := 𝒪) K)))) := by
    intro 𝔭
    refine (CerednikDrinfeld.FormalOmega.T4EAux.forall_not_mem_pullback_iff g (x.pt 0) 𝔭 (stdFullLattice (𝒪 := 𝒪) K)
      (fun u => (u : Fin 2 → K) ∉ latticeMap (edgeFlip K ϖ) (stdLattice 𝒪 K))
      (fun v => (v : Fin 2 → K) ∉ (FullLattice.act (g * edgeFlip K ϖ) (stdFullLattice (𝒪 := 𝒪) K)).1) (fun u => ?_)).symm
    show (u : Fin 2 → K) ∉ latticeMap (edgeFlip K ϖ) (stdLattice 𝒪 K) ↔
      Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) K) (u : Fin 2 → K) ∉ latticeMap (g * edgeFlip K ϖ) (stdLattice 𝒪 K)
    rw [latticeMap_mul, CerednikDrinfeld.FormalOmega.T4EAux.mulVec_mem_latticeMap_iff]
  have T2 : ∀ 𝔭 : Ideal (modPow π R 0),
      (∀ v' : ↥(FullLattice.act (g * edgeFlip K ϖ) (stdFullLattice (𝒪 := 𝒪) K)).1,
          (¬ ∃ w' : ↥(FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1,
              (v' : Fin 2 → K) = (algebraMap 𝒪 K π) • (w' : Fin 2 → K)) →
          (1 : modPow π R 0) ⊗ₜ[𝒪] v' ∉ (x.pt 0).line (FullLattice.act (g * edgeFlip K ϖ) (stdFullLattice (𝒪 := 𝒪) K)) ⊔
            (𝔭 • ⊤ : Submodule (modPow π R 0) (latticeBaseChange 𝒪 K (modPow π R 0) (FullLattice.act (g * edgeFlip K ϖ) (stdFullLattice (𝒪 := 𝒪) K))))) ↔
      (∀ u : ↥(stdFullLattice (𝒪 := 𝒪) K).1,
          (¬ ∃ w' : ↥(stdFullLattice (𝒪 := 𝒪) K).1,
              Matrix.mulVec ((edgeFlip K ϖ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) (u : Fin 2 → K) =
                (algebraMap 𝒪 K π) • (w' : Fin 2 → K)) →
          (1 : modPow π R 0) ⊗ₜ[𝒪] u ∉
            (DeligneDatum.pullback π (modPow π R 0) (g * edgeFlip K ϖ) (x.pt 0)).line (stdFullLattice (𝒪 := 𝒪) K) ⊔
            (𝔭 • ⊤ : Submodule (modPow π R 0) (latticeBaseChange 𝒪 K (modPow π R 0) (stdFullLattice (𝒪 := 𝒪) K)))) := by
    intro 𝔭
    refine (CerednikDrinfeld.FormalOmega.T4EAux.forall_not_mem_pullback_iff (g * edgeFlip K ϖ) (x.pt 0) 𝔭 (stdFullLattice (𝒪 := 𝒪) K)
      (fun u => ¬ ∃ w' : ↥(stdFullLattice (𝒪 := 𝒪) K).1,
              Matrix.mulVec ((edgeFlip K ϖ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) (u : Fin 2 → K) =
                (algebraMap 𝒪 K π) • (w' : Fin 2 → K))
      (fun v' => ¬ ∃ w' : ↥(FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1,
              (v' : Fin 2 → K) = (algebraMap 𝒪 K π) • (w' : Fin 2 → K)) (fun u => ?_)).symm
    refine not_congr ⟨?_, ?_⟩
    · rintro ⟨w', hw'⟩
      refine ⟨latticeMapEquiv g (stdFullLattice (𝒪 := 𝒪) K).1 w', ?_⟩
      rw [coe_latticeMapEquiv_apply, coe_latticeMapEquiv_apply, Units.val_mul, ← Matrix.mulVec_mulVec, hw',
        Matrix.mulVec_smul]
    · rintro ⟨w', hw'⟩
      obtain ⟨w₀, hw₀, hgw₀⟩ := mem_latticeMap.1 w'.2
      refine ⟨⟨w₀, hw₀⟩, ?_⟩
      rw [coe_latticeMapEquiv_apply, Units.val_mul, ← Matrix.mulVec_mulVec, ← hgw₀, ← Matrix.mulVec_smul] at hw'
      have h := congrArg (fun y => Matrix.mulVec ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) y) hw'
      simpa only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, inv_mul_cancel_left, Units.val_one,
        Matrix.one_mulVec] using h

  have hA : (FullLattice.act (g * edgeFlip K ϖ) (stdFullLattice (𝒪 := 𝒪) K)).1 ≤ (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1 := by
    show latticeMap (g * edgeFlip K ϖ) (stdLattice 𝒪 K) ≤ latticeMap g (stdLattice 𝒪 K)
    rw [latticeMap_mul]
    exact latticeMap_mono g (CerednikDrinfeld.FormalOmega.T4EAux.latticeMap_edgeFlip_le hF)
  have hB : ∀ v : ↥(FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1,
      (algebraMap 𝒪 K π) • (v : Fin 2 → K) ∈ (FullLattice.act (g * edgeFlip K ϖ) (stdFullLattice (𝒪 := 𝒪) K)).1 := by
    intro v
    obtain ⟨u, hu, hv⟩ := mem_latticeMap.1 v.2
    show _ ∈ latticeMap (g * edgeFlip K ϖ) (stdLattice 𝒪 K)
    rw [latticeMap_mul, ← hv, ← Matrix.mulVec_smul]
    exact mulVec_mem_latticeMap (CerednikDrinfeld.FormalOmega.T4EAux.smul_mem_latticeMap_edgeFlip hF hu)

  have hwval : ∀ {u : C}, u ∈ affinoid ϖ 0 → Valued.v u = 1 :=
    fun hu => CerednikDrinfeld.FormalOmega.T4EAux.v_eq_one_of_mem_affinoid_zero ϖ hu
  have hlt_iff : 1 < Valued.v ((algebraMap K C ϖ.ϖ)⁻¹ * w) ↔ Valued.v (algebraMap K C ϖ.ϖ) < Valued.v w := by
    rw [map_mul, map_inv₀, ← not_le, CerednikDrinfeld.FormalOmega.T4EAux.inv_mul_le_one_iff hϖ0, not_le]

  have key : ((Valued.v w < 1 ∨ w ∈ affinoid ϖ 0) ∧
        (1 < Valued.v ((algebraMap K C ϖ.ϖ)⁻¹ * w) ∨ (algebraMap K C ϖ.ϖ)⁻¹ * w ∈ affinoid ϖ 0)) ↔
      x.toOmega C ∈ Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪ Omega.edgeTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪
        Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g * edgeFlip K ϖ)) := by
    rw [Set.mem_union, Set.mem_union, Omega.mem_vertexTube_iff, Omega.mem_vertexTube_iff, Omega.mem_edgeTube_iff,
      Omega.mem_stdEdgeTube_iff, hσw, ← hw, hlt_iff]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h1 with h1 | h1
      · rcases h2 with h2 | h2
        · exact Or.inl (Or.inr ⟨hzΩ, hwΩ, h2, h1⟩)
        · exact Or.inr ⟨hzΩ, h2⟩
      · exact Or.inl (Or.inl ⟨hzΩ, h1⟩)
    · rintro (( ⟨-, h⟩ | ⟨-, -, h1, h2⟩ ) | ⟨-, h⟩)
      · refine ⟨Or.inr h, Or.inl ?_⟩
        rw [hwval h]; exact ϖ.lt_one
      · exact ⟨Or.inl h2, Or.inl h1⟩
      · refine ⟨Or.inl ?_, Or.inr h⟩
        have h1 := hwval h
        rw [map_mul, map_inv₀, inv_mul_eq_one₀ hϖ0] at h1
        rw [← h1]; exact ϖ.lt_one

  rw [← key, ← P1, ← P2]
  unfold DeligneDatum.InEdgeChart DeligneDatum.EdgeNondegAt
  constructor
  · intro H
    exact ⟨fun 𝔭 h𝔭 => (T1 𝔭).1 (H 𝔭 h𝔭).2.2.1, fun 𝔭 h𝔭 => (T2 𝔭).1 (H 𝔭 h𝔭).2.2.2⟩
  · rintro ⟨H1, H2⟩ 𝔭 h𝔭
    exact ⟨hA, hB, (T1 𝔭).2 (H1 𝔭 h𝔭), (T2 𝔭).2 (H2 𝔭 h𝔭)⟩

end S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem (solution)
