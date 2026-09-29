-- Prove2me | solution 1 for Deformation.HondaSystem.exists_towerHom_map_comp_eq_comp_of_map_L_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/80d7b7d3-8108-534e-9a83-642d32b7347d

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_PDivisibleGroup_Basic
import Theorems.Thm_Deformation_exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_of_forall_ker_eq_torsionIdeal_zmodp
import Theorems.Thm_Deformation_DieudonneModule_map_injective_and_exists_map_eq_of_isLocalRing_cartierDual
import Theorems.Thm_HopfAlgebra_algHom_eq_of_forall_sub_mem_span_of_isLocalRing_cartierDual
import Theorems.Thm_HopfAlgebra_exists_bialgHom_eq_of_baseChange_eq_of_isLocalRing_cartierDual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_HondaSystem_exists_towerHom_map_comp_eq_comp_of_map_L_le
p2m_attr_erase "instance" "MvFormalGroup.instIsCommAddMv MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode"
p2m_attr_erase "simp" "HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false

universe u

namespace PDMor

open Function
open scoped TensorProduct

universe v w w'

section CompleteDVR

variable {𝓞 : Type u} [CommRing 𝓞] {p : ℕ}
variable {k : Type v} [Field k] [Algebra 𝓞 k]

private theorem isMaximal_span (hk : Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) :
    (Ideal.span {(p : 𝓞)}).IsMaximal :=
  hker ▸ RingHom.ker_isMaximal_of_surjective _ hk

private theorem isLocalRing_of_isAdicComplete [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (hk : Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) : IsLocalRing 𝓞 :=
  haveI := isMaximal_span hk hker
  isLocalRing_of_isAdicComplete_maximal (Ideal.span {(p : 𝓞)})

private theorem isUnit_of_not_mem_span [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (hk : Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) {x : 𝓞}
    (hx : x ∉ Ideal.span {(p : 𝓞)}) : IsUnit x := by
  haveI := isLocalRing_of_isAdicComplete hk hker
  have hmax : IsLocalRing.maximalIdeal 𝓞 = Ideal.span {(p : 𝓞)} :=
    (IsLocalRing.eq_maximalIdeal (isMaximal_span hk hker)).symm
  by_contra h
  exact hx (hmax ▸ (IsLocalRing.mem_maximalIdeal x).2 h)

private theorem span_singleton_pow_eq (n : ℕ) :
    (Ideal.span {(p : 𝓞)}) ^ n • (⊤ : Submodule 𝓞 𝓞) = Ideal.span {(p : 𝓞) ^ n} := by
  rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]

private theorem exists_eq_pow_mul_of_ne_zero [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (hk : Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) {x : 𝓞} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : 𝓞), IsUnit u ∧ x = (p : 𝓞) ^ n * u := by
  classical
  have hex : ∃ n : ℕ, x ∉ Ideal.span {(p : 𝓞) ^ n} := by
    by_contra h
    push Not at h
    apply hx
    refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(p : 𝓞)}) 𝓞) x fun n => ?_
    rw [SModEq.zero, span_singleton_pow_eq]
    exact h n
  let n₀ := Nat.find hex
  have hn₀ : x ∉ Ideal.span {(p : 𝓞) ^ n₀} := Nat.find_spec hex
  have hpos : n₀ ≠ 0 := by
    intro h0
    apply hn₀
    rw [h0, pow_zero, Ideal.span_singleton_one]
    exact Submodule.mem_top
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hxm : x ∈ Ideal.span {(p : 𝓞) ^ m} := by
    by_contra h
    have := Nat.find_min hex (m := m) (by rw [show Nat.find hex = n₀ from rfl, hm]; exact Nat.lt_succ_self m)
    exact this h
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 hxm
  refine ⟨m, u, ?_, by rw [← hu, mul_comm]⟩
  refine isUnit_of_not_mem_span hk hker fun hu' => hn₀ ?_
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hu'
  rw [hm, ← hu, ← hc, Ideal.mem_span_singleton, pow_succ]
  exact ⟨c, by ring⟩

private theorem isDomain_of_isAdicComplete [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (hk : Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) : IsDomain 𝓞 := by
  haveI := isLocalRing_of_isAdicComplete hk hker
  haveI : NoZeroDivisors 𝓞 := ⟨fun {a b} hab => by
    by_contra h
    push Not at h
    obtain ⟨m, u, hu, rfl⟩ := exists_eq_pow_mul_of_ne_zero hk hker h.1
    obtain ⟨n, v, hv, rfl⟩ := exists_eq_pow_mul_of_ne_zero hk hker h.2
    have h1 : u * v * (p : 𝓞) ^ (m + n) = 0 := by rw [← hab]; ring
    have h2 : u * v = 0 := mem_nonZeroDivisors_iff_right.1 (Submonoid.pow_mem _ hp (m + n)) _ h1
    exact (hu.mul hv).ne_zero h2⟩
  exact NoZeroDivisors.to_isDomain 𝓞

private theorem irreducible_natCast [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (hk : Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) : Irreducible (p : 𝓞) := by
  haveI := isLocalRing_of_isAdicComplete hk hker
  have hmax : IsLocalRing.maximalIdeal 𝓞 = Ideal.span {(p : 𝓞)} :=
    (IsLocalRing.eq_maximalIdeal (isMaximal_span hk hker)).symm
  have hpmem : (p : 𝓞) ∈ IsLocalRing.maximalIdeal 𝓞 := hmax ▸ Ideal.mem_span_singleton_self _
  refine ⟨(IsLocalRing.mem_maximalIdeal _).1 hpmem, fun a b hab => ?_⟩
  by_contra h
  push Not at h
  have ha : a ∈ Ideal.span {(p : 𝓞)} := hmax ▸ (IsLocalRing.mem_maximalIdeal a).2 h.1
  have hb : b ∈ Ideal.span {(p : 𝓞)} := hmax ▸ (IsLocalRing.mem_maximalIdeal b).2 h.2
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hb

  have h1 : (1 - (p : 𝓞) * (c * d)) * (p : 𝓞) = 0 := by
    have : (p : 𝓞) = (p : 𝓞) * (p : 𝓞) * (c * d) := by
      conv_lhs => rw [hab, ← hc, ← hd]
      ring
    calc (1 - (p : 𝓞) * (c * d)) * (p : 𝓞) = (p : 𝓞) - (p : 𝓞) * (p : 𝓞) * (c * d) := by ring
      _ = 0 := by rw [← this, sub_self]
  have h2 : 1 - (p : 𝓞) * (c * d) = 0 := mem_nonZeroDivisors_iff_right.1 hp _ h1
  have hunit : IsUnit (p : 𝓞) := isUnit_iff_exists_inv.2 ⟨c * d, (sub_eq_zero.1 h2).symm⟩
  exact (IsLocalRing.mem_maximalIdeal _).1 hpmem hunit

private theorem isDiscreteValuationRing_of_isAdicComplete [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (hk : Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) :
    @IsDiscreteValuationRing 𝓞 _ (isDomain_of_isAdicComplete hp hk hker) := by
  letI := isDomain_of_isAdicComplete hp hk hker
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨(p : 𝓞), irreducible_natCast hp hk hker, fun {x} hx => ?_⟩
  obtain ⟨n, u, hu, rfl⟩ := exists_eq_pow_mul_of_ne_zero hk hker hx
  exact ⟨n, (associated_mul_unit_right ((p : 𝓞) ^ n) u hu)⟩

end CompleteDVR

section Reduction

variable {𝓞 : Type u} [CommRing 𝓞] (k : Type v) [Field k] [Algebra 𝓞 k]
variable {X : Type w} [CommRing X] [Algebra 𝓞 X] {Y : Type w'} [CommRing Y] [Algebra 𝓞 Y]

private noncomputable def red (x : X →ₐ[𝓞] Y) : k ⊗[𝓞] X →ₐ[k] k ⊗[𝓞] Y :=
  Algebra.TensorProduct.map (AlgHom.id k k) x

variable {k}

@[scoped simp] private theorem red_tmul (x : X →ₐ[𝓞] Y) (c : k) (r : X) : red k x (c ⊗ₜ[𝓞] r) = c ⊗ₜ[𝓞] x r := by
  rw [red, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

private theorem red_comp {Z : Type*} [CommRing Z] [Algebra 𝓞 Z] (x : X →ₐ[𝓞] Y) (y : Y →ₐ[𝓞] Z) :
    red k (y.comp x) = (red k y).comp (red k x) := by
  refine Algebra.TensorProduct.ext' fun c r => ?_
  simp [red_tmul]

private theorem sub_mem_span_of_red_eq (hk : Surjective (algebraMap 𝓞 k)) {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    {x x' : X →ₐ[𝓞] Y} (h : red k x = red k x') (r : X) :
    x r - x' r ∈ Ideal.span {(p : Y)} := by
  rw [← Deformation.SpecialFibre.ker_reduction_eq_span (ℛ := Y) hk hker, RingHom.mem_ker,
    Deformation.SpecialFibre.reduction_apply, TensorProduct.tmul_sub, ← red_tmul, ← red_tmul, h, sub_self]

private theorem red_eq_of_forall_sub_mem_span (hk : Surjective (algebraMap 𝓞 k)) {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    {x x' : X →ₐ[𝓞] Y} (h : ∀ r : X, x r - x' r ∈ Ideal.span {(p : Y)}) :
    red k x = red k x' := by
  refine Algebra.TensorProduct.ext' fun c r => ?_
  rw [red_tmul, red_tmul]
  have h1 : (1 : k) ⊗ₜ[𝓞] (x r - x' r) = 0 := by
    have := h r
    rw [← Deformation.SpecialFibre.ker_reduction_eq_span (ℛ := Y) hk hker, RingHom.mem_ker] at this
    exact this
  rw [TensorProduct.tmul_sub, sub_eq_zero] at h1
  calc c ⊗ₜ[𝓞] x r = c • ((1 : k) ⊗ₜ[𝓞] x r) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    _ = c • ((1 : k) ⊗ₜ[𝓞] x' r) := by rw [h1]
    _ = c ⊗ₜ[𝓞] x' r := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end Reduction

section Helpers

variable {𝓞 : Type u} [CommRing 𝓞] {p : ℕ}

private theorem natCast_mem_nonZeroDivisors_of_free (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (X : Type w) [CommRing X] [Algebra 𝓞 X] [Module.Free 𝓞 X] :
    (p : X) ∈ nonZeroDivisors X := by
  refine mem_nonZeroDivisors_iff_right.2 fun x hx => ?_
  have hsm : (p : 𝓞) • x = 0 := by
    rw [Algebra.smul_def, map_natCast, mul_comm]; exact hx
  let b := Module.Free.chooseBasis 𝓞 X
  have hrepr : (p : 𝓞) • b.repr x = 0 := by rw [← map_smul, hsm, map_zero]
  apply b.repr.injective
  rw [map_zero]
  ext i
  have hi := DFunLike.congr_fun hrepr i
  rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.zero_apply, mul_comm] at hi
  exact mem_nonZeroDivisors_iff_right.1 hp _ hi

end Helpers

end PDMor
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_towerHom_map_comp_eq_comp_of_map_L_le.PDMor"

open Function PDMor in
open scoped TensorProduct in
set_option maxHeartbeats 6400000 in

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (L : ℕ → Type u) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra 𝓞 (L v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (L v)] [∀ v, Module.Free 𝓞 (L v)] [∀ v, Module.Finite 𝓞 (L v)]
    (t : ∀ v, L (v + 1) →ₐc[𝓞] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank 𝓞 (L v) = p ^ (v * r))
    (hkerL : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v))
    (hunipL : ∀ v, IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) (L v))))
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L v)))
    (hπs : ∀ v, Function.Surjective (π v))
    (hπk : ∀ v x, π v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y)
    (hπF : ∀ v x, π v (H₁.F x) =
      Deformation.DieudonneModule.frobenius (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L v)) (π v x))
    (hπV : ∀ v x, π v (H₁.V x) =
      Deformation.DieudonneModule.verschiebung (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L v)) (π v x))
    (hπL : ∀ v, (Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight :
          L v →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) (L v)).toRingHom).toAddSubgroup =
      H₁.L.toAddSubgroup.map (π v))
    (hπt : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (t v)) (π (v + 1) x) = π v x)
    (r' : ℕ) (H₂ : Deformation.HondaSystem (p : 𝓞) (Fin r' → 𝓞))
    (L' : ℕ → Type u) [∀ v, CommRing (L' v)] [∀ v, HopfAlgebra 𝓞 (L' v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (L' v)] [∀ v, Module.Free 𝓞 (L' v)] [∀ v, Module.Finite 𝓞 (L' v)]
    (t' : ∀ v, L' (v + 1) →ₐc[𝓞] L' v) (ht' : ∀ v, Function.Surjective (t' v))
    (hrankL' : ∀ v, Module.finrank 𝓞 (L' v) = p ^ (v * r'))
    (hkerL' : ∀ v, RingHom.ker (t' v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L' (v + 1)) (p ^ v))
    (hunipL' : ∀ v, IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) (L' v))))
    (π' : ∀ v, (Fin r' → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L' v)))
    (hπ's : ∀ v, Function.Surjective (π' v))
    (hπ'k : ∀ v x, π' v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y)
    (hπ'F : ∀ v x, π' v (H₂.F x) =
      Deformation.DieudonneModule.frobenius (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L' v)) (π' v x))
    (hπ'V : ∀ v x, π' v (H₂.V x) =
      Deformation.DieudonneModule.verschiebung (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L' v)) (π' v x))
    (hπ'L : ∀ v, (Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight :
          L' v →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) (L' v)).toRingHom).toAddSubgroup =
      H₂.L.toAddSubgroup.map (π' v))
    (hπ't : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (t' v)) (π' (v + 1) x) = π' v x)
    (φ : (Fin r' → 𝓞) →ₗ[𝓞] (Fin r → 𝓞))
    (hφF : φ ∘ₗ H₂.F = H₁.F ∘ₗ φ) (hφV : φ ∘ₗ H₂.V = H₁.V ∘ₗ φ)
    (hφL : Submodule.map φ H₂.L ≤ H₁.L) :
    ∃ f : ∀ v, L' v →ₐc[𝓞] L v,
      (∀ v, (f v).comp (t' v) = (t v).comp (f (v + 1))) ∧
      ∀ v x, Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (f v)) (π' v x) = π v (φ x) := by
  classical
  have hk : Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _
  haveI : IsDomain 𝓞 := isDomain_of_isAdicComplete hp hk hker
  haveI : IsDiscreteValuationRing 𝓞 := isDiscreteValuationRing_of_isAdicComplete hp hk hker
  have hirr : Irreducible (p : 𝓞) := irreducible_natCast hp hk hker

  let D : ℕ → Type u := fun v => Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[𝓞] L v)
  let D' : ℕ → Type u := fun v => Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[𝓞] L' v)

  have hkerle : ∀ v, (π' v).ker ≤ ((π v).comp φ.toAddMonoidHom).ker := by
    intro v x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    obtain ⟨y, rfl⟩ := (hπ'k v x).1 hx
    rw [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, map_smul]
    exact (hπk v _).2 ⟨φ y, rfl⟩
  let φv : ∀ v, D' v →+ D v := fun v =>
    (π' v).liftOfRightInverse (surjInv (hπ's v)) (rightInverse_surjInv (hπ's v))
      ⟨(π v).comp φ.toAddMonoidHom, hkerle v⟩
  have hφv : ∀ v x, φv v (π' v x) = π v (φ x) := fun v x =>
    (π' v).liftOfRightInverse_comp_apply (surjInv (hπ's v)) (rightInverse_surjInv (hπ's v))
      ⟨(π v).comp φ.toAddMonoidHom, hkerle v⟩ x
  have hφvF : ∀ v z, φv v (Deformation.DieudonneModule.frobenius (ZMod p) p _ z) =
      Deformation.DieudonneModule.frobenius (ZMod p) p _ (φv v z) := by
    intro v z
    obtain ⟨x, rfl⟩ := hπ's v z
    rw [← hπ'F, hφv, hφv, show φ (H₂.F x) = H₁.F (φ x) from LinearMap.congr_fun hφF x, hπF]
  have hφvV : ∀ v z, φv v (Deformation.DieudonneModule.verschiebung (ZMod p) p _ z) =
      Deformation.DieudonneModule.verschiebung (ZMod p) p _ (φv v z) := by
    intro v z
    obtain ⟨x, rfl⟩ := hπ's v z
    rw [← hπ'V, hφv, hφv, show φ (H₂.V x) = H₁.V (φ x) from LinearMap.congr_fun hφV x, hπV]

  have hg : ∀ v, ∃ g : (ZMod p) ⊗[𝓞] L' v →ₐc[ZMod p] (ZMod p) ⊗[𝓞] L v,
      Deformation.DieudonneModule.map (ZMod p) p g = φv v := fun v =>
    (Deformation.DieudonneModule.map_injective_and_exists_map_eq_of_isLocalRing_cartierDual p
      ((ZMod p) ⊗[𝓞] L v) ((ZMod p) ⊗[𝓞] L' v) (hunipL v) (hunipL' v)).2 (φv v) (hφvF v) (hφvV v)
  choose g hgφ using hg

  have hχ : ∀ (v n : ℕ) (m : Deformation.wittHom (ZMod p) p n ((ZMod p) ⊗[𝓞] L' v)),
      (m : TruncatedWittVector p n ((ZMod p) ⊗[𝓞] L' v)) ∈ Deformation.TruncWitt.fontaineKer p n
          (Algebra.TensorProduct.includeRight : L' v →ₐ[𝓞] (ZMod p) ⊗[𝓞] L' v).toRingHom →
        Deformation.TruncWitt.map (g v : (ZMod p) ⊗[𝓞] L' v →ₐ[ZMod p] (ZMod p) ⊗[𝓞] L v).toRingHom
            (m : TruncatedWittVector p n ((ZMod p) ⊗[𝓞] L' v)) ∈
          Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight : L v →ₐ[𝓞] (ZMod p) ⊗[𝓞] L v).toRingHom := by
    intro v n m hm
    have h1 : Deformation.DieudonneModule.of (ZMod p) p _ n m ∈ (Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight : L' v →ₐ[𝓞] (ZMod p) ⊗[𝓞] L' v).toRingHom).toAddSubgroup :=
      Deformation.of_mem_fontaineHodge hm
    rw [hπ'L v] at h1
    obtain ⟨l₂, hl₂, hl₂e⟩ := AddSubgroup.mem_map.1 h1
    have h2 : Deformation.DieudonneModule.map (ZMod p) p (g v) (Deformation.DieudonneModule.of (ZMod p) p _ n m) ∈
        (Deformation.fontaineHodge (ZMod p) p
          (Algebra.TensorProduct.includeRight : L v →ₐ[𝓞] (ZMod p) ⊗[𝓞] L v).toRingHom).toAddSubgroup := by
      rw [← hl₂e, hgφ, hφv, hπL v]
      exact AddSubgroup.mem_map.2 ⟨φ l₂, hφL ⟨l₂, hl₂, rfl⟩, rfl⟩
    rw [Deformation.DieudonneModule.map_of] at h2
    change Deformation.DieudonneModule.of (ZMod p) p _ n (Deformation.wittHomMap p n (g v) m) ∈
      Deformation.fontaineHodge (ZMod p) p _ at h2
    rw [Deformation.of_mem_fontaineHodge_iff (natCast_mem_nonZeroDivisors_of_free hp (L v))
      (le_of_eq (Deformation.SpecialFibre.ker_reduction_eq_span hk hker))
      (Deformation.SpecialFibre.reduction_surjective hk)] at h2
    simpa [Deformation.coe_wittHomMap] using h2

  have hf : ∀ v, ∃ fv : L' v →ₐc[𝓞] L v,
      Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (fv : L' v →ₐ[𝓞] L v) =
        (g v : (ZMod p) ⊗[𝓞] L' v →ₐ[ZMod p] (ZMod p) ⊗[𝓞] L v) := by
    intro v
    obtain ⟨x, hx⟩ := Deformation.exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_of_forall_ker_eq_torsionIdeal_zmodp p hp hker r' L' t' ht' hrankL' hkerL' hunipL' v (L v)
      (g v : (ZMod p) ⊗[𝓞] L' v →ₐ[ZMod p] (ZMod p) ⊗[𝓞] L v) (hχ v)
    obtain ⟨Φ, hΦ⟩ := HopfAlgebra.exists_bialgHom_eq_of_baseChange_eq_of_isLocalRing_cartierDual 𝓞 p hirr
      (ZMod p) hk hker (L v) (L' v) ⟨v * r', hrankL' v⟩ (hunipL' v) (g v) x hx
    exact ⟨Φ, by rw [hΦ]; exact hx⟩
  choose f hfg using hf
  have hfφ : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (f v)) (π' v x) = π v (φ x) := by
    intro v x
    have : Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (f v) = g v := by
      apply DFunLike.ext
      intro z
      exact AlgHom.congr_fun (hfg v) z
    rw [this, hgφ, hφv]

  have hfaith : ∀ (v : ℕ) (G₁ G₂ : (ZMod p) ⊗[𝓞] L' (v + 1) →ₐc[ZMod p] (ZMod p) ⊗[𝓞] L v),
      Deformation.DieudonneModule.map (ZMod p) p G₁ = Deformation.DieudonneModule.map (ZMod p) p G₂ → G₁ = G₂ :=
    fun v => (Deformation.DieudonneModule.map_injective_and_exists_map_eq_of_isLocalRing_cartierDual p
      ((ZMod p) ⊗[𝓞] L v) ((ZMod p) ⊗[𝓞] L' (v + 1)) (hunipL v) (hunipL' (v + 1))).1
  have hmapcomp : ∀ {X Y Z : Type u} [CommRing X] [HopfAlgebra 𝓞 X] [CommRing Y] [HopfAlgebra 𝓞 Y]
      [CommRing Z] [HopfAlgebra 𝓞 Z] (G₁ : X →ₐc[𝓞] Y) (G₂ : Y →ₐc[𝓞] Z),
      Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (G₂.comp G₁) =
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) G₂).comp
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) G₁) := by
    intro X Y Z _ _ _ _ _ _ G₁ G₂
    apply DFunLike.ext
    intro z
    change Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) ((G₂ : Y →ₐ[𝓞] Z).comp (G₁ : X →ₐ[𝓞] Y)) z =
      Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (G₂ : Y →ₐ[𝓞] Z)
        (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (G₁ : X →ₐ[𝓞] Y) z)
    rw [show (AlgHom.id (ZMod p) (ZMod p)) = (AlgHom.id (ZMod p) (ZMod p)).comp (AlgHom.id (ZMod p) (ZMod p))
      from rfl, Algebra.TensorProduct.map_comp]
    rfl
  have hcompat : ∀ v, (f v).comp (t' v) = (t v).comp (f (v + 1)) := by
    intro v

    have hsf : Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ((f v).comp (t' v)) =
        Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ((t v).comp (f (v + 1))) := by
      apply hfaith v
      ext z
      obtain ⟨x, rfl⟩ := hπ's (v + 1) z
      rw [hmapcomp, hmapcomp, Deformation.DieudonneModule.map_comp, Deformation.DieudonneModule.map_comp,
        hπ't, hfφ, hfφ, hπt]

    have hred : red (ZMod p) ((f v).comp (t' v) : L' (v + 1) →ₐ[𝓞] L v) =
        red (ZMod p) ((t v).comp (f (v + 1)) : L' (v + 1) →ₐ[𝓞] L v) := by
      apply AlgHom.ext
      intro z
      exact DFunLike.congr_fun hsf z
    have halg := HopfAlgebra.algHom_eq_of_forall_sub_mem_span_of_isLocalRing_cartierDual 𝓞 p hirr (ZMod p) hk hker
      (L' (v + 1)) ⟨(v + 1) * r', hrankL' (v + 1)⟩ (hunipL' (v + 1)) (L v)
      ((f v).comp (t' v) : L' (v + 1) →ₐ[𝓞] L v) ((t v).comp (f (v + 1)) : L' (v + 1) →ₐ[𝓞] L v)
      (sub_mem_span_of_red_eq hk hker hred)
    apply DFunLike.ext
    intro z
    exact AlgHom.congr_fun halg z
  exact ⟨f, hcompat, hfφ⟩

end S_Deformation_HondaSystem_exists_towerHom_map_comp_eq_comp_of_map_L_le
end P2MW
export P2MW.S_Deformation_HondaSystem_exists_towerHom_map_comp_eq_comp_of_map_L_le (solution)
