-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.AdicPoint.inEdgeChart_pt_iff_inEdgeChart_pt_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/278fea75-7d15-5d90-a538-c1bf7588e5f4

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_pt_iff_inEdgeChart_pt_zero

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
p2m_open "LT.LatticeTree CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_pt_iff_inEdgeChart_pt_zero.CerednikDrinfeld CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_pt_iff_inEdgeChart_pt_zero.CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega"

namespace CerednikDrinfeld
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "DeligneDatum.VertexNondegAt DeligneDatum.EdgeNondegAt modPow modPowTransition AdicPoint rTensor_one_tmul rTensor_smul_left DeligneDatum.map Omega latticeBaseChange DeligneDatum lineBaseChange"
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

open CerednikDrinfeld.FormalOmega.LevelAux in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪}
    {R : Type} [CommRing R] [Algebra 𝒪 R] (x : AdicPoint K π R) (n : ℕ) (M' M : FullLattice 𝒪 K) :
    (x.pt n).InEdgeChart π M' M ↔ (x.pt 0).InEdgeChart π M' M := by
  rw [← map_red_pt x n]
  constructor
  · intro h 𝔭' h𝔭'
    haveI := h𝔭'
    rw [edgeNondegAt_map_iff (red π n) (red_surjective π n)]
    exact h _ (Ideal.IsPrime.comap _)
  · intro h 𝔮 h𝔮
    haveI := h𝔮
    haveI : (Ideal.map (red (R := R) π n) 𝔮).IsPrime :=
      Ideal.map_isPrime_of_surjective (red_surjective π n) (ker_red_le π n 𝔮)
    have := h (Ideal.map (red (R := R) π n) 𝔮) this
    rw [edgeNondegAt_map_iff (red π n) (red_surjective π n), comap_map_red] at this
    exact this

end S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_pt_iff_inEdgeChart_pt_zero
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_pt_iff_inEdgeChart_pt_zero (solution)
