-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isTranslateOdd_of_det_mul_eq_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c068cc3e-b710-5bd0-973f-2c475281e46c

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isTranslateOdd_of_det_mul_eq_algebraMap

set_option autoImplicit false

open scoped TensorProduct Matrix
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace ReduceTE

theorem exists_eq_unit_mul_zpow {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π) (x : Kˣ) :
    ∃ (n : ℤ) (u : 𝒪ˣ), (x : K) = algebraMap 𝒪 K u * algebraMap 𝒪 K π ^ n := by
  have hπK : algebraMap 𝒪 K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective 𝒪 K)).mpr hπ.ne_zero
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective (A := 𝒪) (x : K)
  have ha : a ≠ 0 := by
    rintro rfl; rw [map_zero, zero_div] at hx; exact x.ne_zero hx.symm
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨i, ua, hua⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hπ
  obtain ⟨j, ub, hub⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hπ

  refine ⟨(i : ℤ) - (j : ℤ), ua⁻¹ * ub, ?_⟩
  have hbK : algebraMap 𝒪 K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective 𝒪 K)).mpr hb0
  have ea : algebraMap 𝒪 K a = algebraMap 𝒪 K π ^ i * algebraMap 𝒪 K ((ua⁻¹ : 𝒪ˣ) : 𝒪) := by
    rw [← map_pow, ← map_mul, ← hua, mul_assoc, Units.mul_inv, mul_one]
  have eb : algebraMap 𝒪 K b = algebraMap 𝒪 K π ^ j * algebraMap 𝒪 K ((ub⁻¹ : 𝒪ˣ) : 𝒪) := by
    rw [← map_pow, ← map_mul, ← hub, mul_assoc, Units.mul_inv, mul_one]
  have hπj : algebraMap 𝒪 K π ^ j ≠ 0 := pow_ne_zero _ hπK
  have hub1 : algebraMap 𝒪 K (ub : 𝒪) * algebraMap 𝒪 K ((ub⁻¹ : 𝒪ˣ) : 𝒪) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [← hx, div_eq_iff hbK, zpow_sub₀ hπK, zpow_natCast, zpow_natCast, ea, eb, Units.val_mul, map_mul]
  field_simp
  linear_combination (-1 : K) * hub1

theorem hasDetIndex_latticeMap {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    (hπK : algebraMap 𝒪 K π ≠ 0) {N : Submodule 𝒪 (Fin 2 → K)} {e : ℤ} (hN : HasDetIndex π N e)
    (m : Matrix.GeneralLinearGroup (Fin 2) K) {n : ℤ} {w : 𝒪ˣ}
    (hm : ((Matrix.GeneralLinearGroup.det m : Kˣ) : K) = algebraMap 𝒪 K w * algebraMap 𝒪 K π ^ n) :
    HasDetIndex π (latticeMap m N) (n + e) := by
  obtain ⟨g, hg, u, hu⟩ := hN
  refine ⟨m * g, by rw [latticeMap_mul, hg], w * u, ?_⟩
  rw [map_mul, Units.val_mul, hm, hu, Units.val_mul, map_mul, zpow_add₀ hπK]
  ring

end ReduceTE

namespace ReduceTE

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem mulVec_inv_mulVec (m : Matrix.GeneralLinearGroup (Fin 2) K) (v : Fin 2 → K) :
    (m : Matrix (Fin 2) (Fin 2) K) *ᵥ (((m⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem inv_mulVec_mulVec (m : Matrix.GeneralLinearGroup (Fin 2) K) (v : Fin 2 → K) :
    (((m⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ ((m : Matrix (Fin 2) (Fin 2) K) *ᵥ v)) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem inv_mulVec_mem_of_mem_latticeMap {m : Matrix.GeneralLinearGroup (Fin 2) K} {L : Submodule 𝒪 (Fin 2 → K)}
    {v : Fin 2 → K} (hv : v ∈ latticeMap m L) :
    (((m⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v) ∈ L := by
  obtain ⟨w, hw, rfl⟩ := mem_latticeMap.mp hv
  rwa [inv_mulVec_mulVec]

theorem mem_latticeMap_iff_inv_mulVec_mem {m : Matrix.GeneralLinearGroup (Fin 2) K} {L : Submodule 𝒪 (Fin 2 → K)}
    {v : Fin 2 → K} :
    v ∈ latticeMap m L ↔ (((m⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v) ∈ L :=
  ⟨inv_mulVec_mem_of_mem_latticeMap, fun h => by
    have := mulVec_mem_latticeMap (g := m) h; rwa [mulVec_inv_mulVec] at this⟩

theorem actBaseChange_symm_one_tmul (R : Type) [CommRing R] [Algebra 𝒪 R] (m : Matrix.GeneralLinearGroup (Fin 2) K)
    (M : FullLattice 𝒪 K) (v : Fin 2 → K) (hv : v ∈ (FullLattice.act m M).1) :
    (actBaseChange R m M).symm ((1 : R) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(FullLattice.act m M).1)) =
      (1 : R) ⊗ₜ[𝒪] (⟨_, inv_mulVec_mem_of_mem_latticeMap hv⟩ : ↥M.1) := by
  rw [LinearEquiv.symm_apply_eq, actBaseChange_tmul]
  congr 1
  apply Subtype.ext
  rw [coe_latticeMapEquiv_apply]
  exact (mulVec_inv_mulVec m v).symm

theorem actBaseChange_smulInto (R : Type) [CommRing R] [Algebra 𝒪 R] (m : Matrix.GeneralLinearGroup (Fin 2) K)
    {L₀ L₁ : FullLattice 𝒪 K} (h : ∀ v ∈ L₁.1, algebraMap 𝒪 K π • v ∈ L₀.1)
    (h' : ∀ v ∈ (FullLattice.act m L₁).1, algebraMap 𝒪 K π • v ∈ (FullLattice.act m L₀).1)
    (y : latticeBaseChange 𝒪 K R L₁) :
    ((smulInto π h').baseChange R : latticeBaseChange 𝒪 K R (FullLattice.act m L₁) →ₗ[R] latticeBaseChange 𝒪 K R (FullLattice.act m L₀))
        (actBaseChange R m L₁ y) =
      actBaseChange R m L₀ (((smulInto π h).baseChange R : latticeBaseChange 𝒪 K R L₁ →ₗ[R] latticeBaseChange 𝒪 K R L₀) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero]
  | add y z hy hz => simp only [LinearEquiv.map_add, LinearMap.map_add, hy, hz]
  | tmul b v =>
    rw [actBaseChange_tmul]
    change b ⊗ₜ[𝒪] (smulInto π h' (latticeMapEquiv m L₁.1 v)) = actBaseChange R m L₀ (b ⊗ₜ[𝒪] (smulInto π h v))
    rw [actBaseChange_tmul]
    congr 1
    apply Subtype.ext
    rw [coe_smulInto_apply, coe_latticeMapEquiv_apply, coe_latticeMapEquiv_apply, coe_smulInto_apply, Matrix.mulVec_smul]

theorem hasDetIndex_latticeMap_of_det_eq (π : 𝒪) {N : Submodule 𝒪 (Fin 2 → K)} {k : ℤ} (hN : HasDetIndex π N k)
    (m : Matrix.GeneralLinearGroup (Fin 2) K) {e : 𝒪ˣ}
    (hm : ((Matrix.GeneralLinearGroup.det m : Kˣ) : K) = algebraMap 𝒪 K e) :
    HasDetIndex π (latticeMap m N) k := by
  obtain ⟨g, hg, u, hu⟩ := hN
  refine ⟨m * g, by rw [latticeMap_mul, hg], e * u, ?_⟩
  rw [map_mul, Units.val_mul, hm, hu, Units.val_mul, map_mul, mul_assoc]

noncomputable def evenTranslate (Q : DrinfeldDatum (K := K) π B) (m : Matrix.GeneralLinearGroup (Fin 2) K) (e : 𝒪ˣ)
    (hm : ((Matrix.GeneralLinearGroup.det m : Kˣ) : K) = algebraMap 𝒪 K e) :
    DrinfeldDatum (K := K) π B where
  N₀ x := latticeMap m (Q.N₀ x)
  N₁ x := latticeMap m (Q.N₁ x)
  full₀ x := (Q.full₀ x).map m
  full₁ x := (Q.full₁ x).map m
  le x := latticeMap_mono m (Q.le x)
  smul_le x v hv := by
    obtain ⟨v₀, hv₀, rfl⟩ := mem_latticeMap.mp hv
    rw [← Matrix.mulVec_smul]
    exact mulVec_mem_latticeMap (Q.smul_le x v₀ hv₀)
  isOpen_setOf_mem₀ v := by
    have : {x : PrimeSpectrum B | v ∈ latticeMap m (Q.N₀ x)} =
        {x | (((m⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v) ∈ Q.N₀ x} := by
      ext x; exact mem_latticeMap_iff_inv_mulVec_mem
    rw [this]; exact Q.isOpen_setOf_mem₀ _
  isOpen_setOf_mem₁ v := by
    have : {x : PrimeSpectrum B | v ∈ latticeMap m (Q.N₁ x)} =
        {x | (((m⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v) ∈ Q.N₁ x} := by
      ext x; exact mem_latticeMap_iff_inv_mulVec_mem
    rw [this]; exact Q.isOpen_setOf_mem₁ _
  T₀ := Q.T₀
  T₁ := Q.T₁
  invertible₀ := Q.invertible₀
  invertible₁ := Q.invertible₁
  Pi₀ := Q.Pi₀
  Pi₁ := Q.Pi₁
  Pi₁_Pi₀ := Q.Pi₁_Pi₀
  Pi₀_Pi₁ := Q.Pi₀_Pi₁
  u₀ x := (Q.u₀ x).comp (actBaseChange (locRing B x) m (Q.L₀ x)).symm.toLinearMap
  u₁ x := (Q.u₁ x).comp (actBaseChange (locRing B x) m (Q.L₁ x)).symm.toLinearMap
  u₁_incl x w' := by
    show Q.u₁ x ((actBaseChange (locRing B x) m (Q.L₁ x)).symm (inclBaseChange (locRing B x) (latticeMap_mono m (Q.le x)) w')) =
      LocalizedModule.map x.asIdeal.primeCompl Q.Pi₀ (Q.u₀ x ((actBaseChange (locRing B x) m (Q.L₀ x)).symm w'))
    rw [← Q.u₁_incl x ((actBaseChange (locRing B x) m (Q.L₀ x)).symm w')]
    congr 1
    rw [LinearEquiv.symm_apply_eq]
    have h := actBaseChange_inclBaseChange (B := locRing B x) m (M' := Q.L₀ x) (M := Q.L₁ x) (Q.le x) ((actBaseChange (locRing B x) m (Q.L₀ x)).symm w')
    rw [LinearEquiv.coe_toLinearMap, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply] at h
    exact h.symm
  u₀_smul x w' := by
    show Q.u₀ x ((actBaseChange (locRing B x) m (Q.L₀ x)).symm
        (((smulInto π _).baseChange (locRing B x) : _ →ₗ[locRing B x] _) w')) =
      LocalizedModule.map x.asIdeal.primeCompl Q.Pi₁ (Q.u₁ x ((actBaseChange (locRing B x) m (Q.L₁ x)).symm w'))
    rw [← Q.u₀_smul x ((actBaseChange (locRing B x) m (Q.L₁ x)).symm w')]
    congr 1
    rw [LinearEquiv.symm_apply_eq]
    have h := actBaseChange_smulInto (π := π) (locRing B x) m (L₀ := Q.L₀ x) (L₁ := Q.L₁ x) (Q.smul_le x)
      (fun v hv => by
        obtain ⟨v₀, hv₀, rfl⟩ := mem_latticeMap.mp hv
        rw [← Matrix.mulVec_smul]
        exact mulVec_mem_latticeMap (Q.smul_le x v₀ hv₀))
      ((actBaseChange (locRing B x) m (Q.L₁ x)).symm w')
    rw [LinearEquiv.apply_symm_apply] at h
    exact h
  u₀_surjective x := (Q.u₀_surjective x).comp (actBaseChange (locRing B x) m (Q.L₀ x)).symm.surjective
  u₁_surjective x := (Q.u₁_surjective x).comp (actBaseChange (locRing B x) m (Q.L₁ x)).symm.surjective
  u₀_continuous x v hv := by
    obtain ⟨f, t, hf, hcont⟩ := Q.u₀_continuous x _ (inv_mulVec_mem_of_mem_latticeMap hv)
    refine ⟨f, t, hf, fun y hy => ?_⟩
    obtain ⟨hv₀, hu⟩ := hcont y hy
    refine ⟨mem_latticeMap_iff_inv_mulVec_mem.mpr hv₀, ?_⟩
    show Q.u₀ y ((actBaseChange (locRing B y) m (Q.L₀ y)).symm ((1 : locRing B y) ⊗ₜ[𝒪] ⟨v, _⟩)) = _
    rw [actBaseChange_symm_one_tmul]
    exact hu
  u₁_continuous x v hv := by
    obtain ⟨f, t, hf, hcont⟩ := Q.u₁_continuous x _ (inv_mulVec_mem_of_mem_latticeMap hv)
    refine ⟨f, t, hf, fun y hy => ?_⟩
    obtain ⟨hv₀, hu⟩ := hcont y hy
    refine ⟨mem_latticeMap_iff_inv_mulVec_mem.mpr hv₀, ?_⟩
    show Q.u₁ y ((actBaseChange (locRing B y) m (Q.L₁ y)).symm ((1 : locRing B y) ⊗ₜ[𝒪] ⟨v, _⟩)) = _
    rw [actBaseChange_symm_one_tmul]
    exact hu
  locallyConstant₀ x hx := by
    obtain ⟨U, hU, hxU, hloc⟩ := Q.locallyConstant₀ x hx
    exact ⟨U, hU, hxU, fun y hy hyS => by rw [hloc y hy hyS]⟩
  locallyConstant₁ x hx := by
    obtain ⟨U, hU, hxU, hloc⟩ := Q.locallyConstant₁ x hx
    exact ⟨U, hU, hxU, fun y hy hyS => by rw [hloc y hy hyS]⟩
  injective₀ x v hmem := by
    obtain ⟨v, hv⟩ := v
    have hv' := inv_mulVec_mem_of_mem_latticeMap hv
    have e : ((Q.u₀ x).comp (actBaseChange (locRing B x) m (Q.L₀ x)).symm.toLinearMap)
        ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(latticeMap m (Q.N₀ x)))) =
        Q.u₀ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨_, hv'⟩ : ↥(Q.N₀ x))) := by
      show Q.u₀ x ((actBaseChange (locRing B x) m (Q.L₀ x)).symm ((1 : locRing B x) ⊗ₜ[𝒪] ⟨v, hv⟩)) = _
      rw [actBaseChange_symm_one_tmul]
    erw [e] at hmem
    obtain ⟨w, hw, hvw⟩ := Q.injective₀ x ⟨_, hv'⟩ hmem
    refine ⟨(m : Matrix (Fin 2) (Fin 2) K) *ᵥ w, mulVec_mem_latticeMap hw, ?_⟩
    show v = algebraMap 𝒪 K π • ((m : Matrix (Fin 2) (Fin 2) K) *ᵥ w)
    rw [← Matrix.mulVec_smul, ← hvw, mulVec_inv_mulVec]
  injective₁ x v hmem := by
    obtain ⟨v, hv⟩ := v
    have hv' := inv_mulVec_mem_of_mem_latticeMap hv
    have e : ((Q.u₁ x).comp (actBaseChange (locRing B x) m (Q.L₁ x)).symm.toLinearMap)
        ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(latticeMap m (Q.N₁ x)))) =
        Q.u₁ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨_, hv'⟩ : ↥(Q.N₁ x))) := by
      show Q.u₁ x ((actBaseChange (locRing B x) m (Q.L₁ x)).symm ((1 : locRing B x) ⊗ₜ[𝒪] ⟨v, hv⟩)) = _
      rw [actBaseChange_symm_one_tmul]
    erw [e] at hmem
    have hw := Q.injective₁ x ⟨_, hv'⟩ hmem
    show v ∈ latticeMap m (Q.N₀ x)
    exact mem_latticeMap_iff_inv_mulVec_mem.mpr hw
  hasDetIndex₀ x hx := hasDetIndex_latticeMap_of_det_eq π (Q.hasDetIndex₀ x hx) m hm
  hasDetIndex₁ x hx := hasDetIndex_latticeMap_of_det_eq π (Q.hasDetIndex₁ x hx) m hm

end ReduceTE

namespace ReduceTE

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem incl_actBaseChange_eq_actBaseChange_smulInto (R : Type) [CommRing R] [Algebra 𝒪 R]
    (h₀ h₁ : Matrix.GeneralLinearGroup (Fin 2) K)
    (hh : ∀ v : Fin 2 → K, (h₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ v = algebraMap 𝒪 K π • ((h₁ : Matrix (Fin 2) (Fin 2) K) *ᵥ v))
    {L₀ L₁ : FullLattice 𝒪 K} (h : ∀ v ∈ L₁.1, algebraMap 𝒪 K π • v ∈ L₀.1)
    (hle : (FullLattice.act h₀ L₁).1 ≤ (FullLattice.act h₁ L₀).1) (y : latticeBaseChange 𝒪 K R L₁) :
    inclBaseChange R hle (actBaseChange R h₀ L₁ y) =
      actBaseChange R h₁ L₀ (((smulInto π h).baseChange R : latticeBaseChange 𝒪 K R L₁ →ₗ[R] latticeBaseChange 𝒪 K R L₀) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero]
  | add y z hy hz => simp only [LinearEquiv.map_add, LinearMap.map_add, hy, hz]
  | tmul b v =>
    rw [actBaseChange_tmul]
    change b ⊗ₜ[𝒪] (Submodule.inclusion hle (latticeMapEquiv h₀ L₁.1 v)) = actBaseChange R h₁ L₀ (b ⊗ₜ[𝒪] (smulInto π h v))
    rw [actBaseChange_tmul]
    congr 1
    apply Subtype.ext
    rw [Submodule.coe_inclusion, coe_latticeMapEquiv_apply, coe_latticeMapEquiv_apply, coe_smulInto_apply, Matrix.mulVec_smul]
    exact hh _

theorem smulInto_actBaseChange_eq_actBaseChange_incl (R : Type) [CommRing R] [Algebra 𝒪 R]
    (h₀ h₁ : Matrix.GeneralLinearGroup (Fin 2) K)
    (hh : ∀ v : Fin 2 → K, (h₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ v = algebraMap 𝒪 K π • ((h₁ : Matrix (Fin 2) (Fin 2) K) *ᵥ v))
    {L₀ L₁ : FullLattice 𝒪 K} (hle : L₀.1 ≤ L₁.1)
    (h' : ∀ v ∈ (FullLattice.act h₁ L₀).1, algebraMap 𝒪 K π • v ∈ (FullLattice.act h₀ L₁).1)
    (y : latticeBaseChange 𝒪 K R L₀) :
    ((smulInto π h').baseChange R : latticeBaseChange 𝒪 K R (FullLattice.act h₁ L₀) →ₗ[R] latticeBaseChange 𝒪 K R (FullLattice.act h₀ L₁))
        (actBaseChange R h₁ L₀ y) =
      actBaseChange R h₀ L₁ (inclBaseChange R hle y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero]
  | add y z hy hz => simp only [LinearEquiv.map_add, LinearMap.map_add, hy, hz]
  | tmul b v =>
    rw [actBaseChange_tmul]
    change b ⊗ₜ[𝒪] (smulInto π h' (latticeMapEquiv h₁ L₀.1 v)) = actBaseChange R h₀ L₁ (b ⊗ₜ[𝒪] (Submodule.inclusion hle v))
    rw [actBaseChange_tmul]
    congr 1
    apply Subtype.ext
    rw [coe_smulInto_apply, coe_latticeMapEquiv_apply, coe_latticeMapEquiv_apply, Submodule.coe_inclusion]
    exact (hh _).symm

noncomputable def oddTranslate (Q : DrinfeldDatum (K := K) π B) (h₀ h₁ : Matrix.GeneralLinearGroup (Fin 2) K)
    (hh : ∀ v : Fin 2 → K, (h₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ v = algebraMap 𝒪 K π • ((h₁ : Matrix (Fin 2) (Fin 2) K) *ᵥ v))
    (hπK : algebraMap 𝒪 K π ≠ 0) (e : 𝒪ˣ)
    (hdet₀ : ((Matrix.GeneralLinearGroup.det h₀ : Kˣ) : K) = algebraMap 𝒪 K e * algebraMap 𝒪 K π ^ (1 : ℤ))
    (hdet₁ : ((Matrix.GeneralLinearGroup.det h₁ : Kˣ) : K) = algebraMap 𝒪 K e * algebraMap 𝒪 K π ^ (-1 : ℤ)) :
    DrinfeldDatum (K := K) π B where
  N₀ x := latticeMap h₀ (Q.N₁ x)
  N₁ x := latticeMap h₁ (Q.N₀ x)
  full₀ x := (Q.full₁ x).map h₀
  full₁ x := (Q.full₀ x).map h₁
  le x := by
    rintro _ ⟨w, hw, rfl⟩
    show (h₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ w ∈ latticeMap h₁ (Q.N₀ x)
    rw [hh, ← Matrix.mulVec_smul]
    exact mulVec_mem_latticeMap (Q.smul_le x w hw)
  smul_le x v hv := by
    obtain ⟨v₀, hv₀, rfl⟩ := mem_latticeMap.mp hv
    show algebraMap 𝒪 K π • ((h₁ : Matrix (Fin 2) (Fin 2) K) *ᵥ v₀) ∈ latticeMap h₀ (Q.N₁ x)
    rw [← hh]
    exact mulVec_mem_latticeMap (Q.le x hv₀)
  isOpen_setOf_mem₀ v := by
    have : {x : PrimeSpectrum B | v ∈ latticeMap h₀ (Q.N₁ x)} =
        {x | (((h₀⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v) ∈ Q.N₁ x} := by
      ext x; exact mem_latticeMap_iff_inv_mulVec_mem
    rw [this]; exact Q.isOpen_setOf_mem₁ _
  isOpen_setOf_mem₁ v := by
    have : {x : PrimeSpectrum B | v ∈ latticeMap h₁ (Q.N₀ x)} =
        {x | (((h₁⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v) ∈ Q.N₀ x} := by
      ext x; exact mem_latticeMap_iff_inv_mulVec_mem
    rw [this]; exact Q.isOpen_setOf_mem₀ _
  T₀ := Q.T₁
  T₁ := Q.T₀
  invertible₀ := Q.invertible₁
  invertible₁ := Q.invertible₀
  Pi₀ := Q.Pi₁
  Pi₁ := Q.Pi₀
  Pi₁_Pi₀ := Q.Pi₀_Pi₁
  Pi₀_Pi₁ := Q.Pi₁_Pi₀
  u₀ x := (Q.u₁ x).comp (actBaseChange (locRing B x) h₀ (Q.L₁ x)).symm.toLinearMap
  u₁ x := (Q.u₀ x).comp (actBaseChange (locRing B x) h₁ (Q.L₀ x)).symm.toLinearMap
  u₁_incl x w' := by
    show Q.u₀ x ((actBaseChange (locRing B x) h₁ (Q.L₀ x)).symm (inclBaseChange (locRing B x) _ w')) =
      LocalizedModule.map x.asIdeal.primeCompl Q.Pi₁ (Q.u₁ x ((actBaseChange (locRing B x) h₀ (Q.L₁ x)).symm w'))
    rw [← Q.u₀_smul x ((actBaseChange (locRing B x) h₀ (Q.L₁ x)).symm w')]
    congr 1
    rw [LinearEquiv.symm_apply_eq]
    have hnat := incl_actBaseChange_eq_actBaseChange_smulInto (π := π) (locRing B x) h₀ h₁ hh (L₀ := Q.L₀ x) (L₁ := Q.L₁ x)
      (Q.smul_le x) (by
        rintro _ ⟨w, hw, rfl⟩
        show (h₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ w ∈ latticeMap h₁ (Q.N₀ x)
        rw [hh, ← Matrix.mulVec_smul]
        exact mulVec_mem_latticeMap (Q.smul_le x w hw)) ((actBaseChange (locRing B x) h₀ (Q.L₁ x)).symm w')
    rw [LinearEquiv.apply_symm_apply] at hnat
    exact hnat
  u₀_smul x w' := by
    show Q.u₁ x ((actBaseChange (locRing B x) h₀ (Q.L₁ x)).symm
        (((smulInto π _).baseChange (locRing B x) : _ →ₗ[locRing B x] _) w')) =
      LocalizedModule.map x.asIdeal.primeCompl Q.Pi₀ (Q.u₀ x ((actBaseChange (locRing B x) h₁ (Q.L₀ x)).symm w'))
    rw [← Q.u₁_incl x ((actBaseChange (locRing B x) h₁ (Q.L₀ x)).symm w')]
    congr 1
    rw [LinearEquiv.symm_apply_eq]
    have hnat := smulInto_actBaseChange_eq_actBaseChange_incl (π := π) (locRing B x) h₀ h₁ hh (L₀ := Q.L₀ x) (L₁ := Q.L₁ x)
      (Q.le x) (fun v hv => by
        obtain ⟨v₀, hv₀, rfl⟩ := mem_latticeMap.mp hv
        show algebraMap 𝒪 K π • ((h₁ : Matrix (Fin 2) (Fin 2) K) *ᵥ v₀) ∈ latticeMap h₀ (Q.N₁ x)
        rw [← hh]
        exact mulVec_mem_latticeMap (Q.le x hv₀)) ((actBaseChange (locRing B x) h₁ (Q.L₀ x)).symm w')
    rw [LinearEquiv.apply_symm_apply] at hnat
    exact hnat
  u₀_surjective x := (Q.u₁_surjective x).comp (actBaseChange (locRing B x) h₀ (Q.L₁ x)).symm.surjective
  u₁_surjective x := (Q.u₀_surjective x).comp (actBaseChange (locRing B x) h₁ (Q.L₀ x)).symm.surjective
  u₀_continuous x v hv := by
    obtain ⟨f, t, hf, hcont⟩ := Q.u₁_continuous x _ (inv_mulVec_mem_of_mem_latticeMap hv)
    refine ⟨f, t, hf, fun y hy => ?_⟩
    obtain ⟨hv₀, hu⟩ := hcont y hy
    refine ⟨mem_latticeMap_iff_inv_mulVec_mem.mpr hv₀, ?_⟩
    show Q.u₁ y ((actBaseChange (locRing B y) h₀ (Q.L₁ y)).symm ((1 : locRing B y) ⊗ₜ[𝒪] ⟨v, _⟩)) = _
    rw [actBaseChange_symm_one_tmul]
    exact hu
  u₁_continuous x v hv := by
    obtain ⟨f, t, hf, hcont⟩ := Q.u₀_continuous x _ (inv_mulVec_mem_of_mem_latticeMap hv)
    refine ⟨f, t, hf, fun y hy => ?_⟩
    obtain ⟨hv₀, hu⟩ := hcont y hy
    refine ⟨mem_latticeMap_iff_inv_mulVec_mem.mpr hv₀, ?_⟩
    show Q.u₀ y ((actBaseChange (locRing B y) h₁ (Q.L₀ y)).symm ((1 : locRing B y) ⊗ₜ[𝒪] ⟨v, _⟩)) = _
    rw [actBaseChange_symm_one_tmul]
    exact hu
  locallyConstant₀ x hx := by
    obtain ⟨U, hU, hxU, hloc⟩ := Q.locallyConstant₁ x hx
    exact ⟨U, hU, hxU, fun y hy hyS => by rw [hloc y hy hyS]⟩
  locallyConstant₁ x hx := by
    obtain ⟨U, hU, hxU, hloc⟩ := Q.locallyConstant₀ x hx
    exact ⟨U, hU, hxU, fun y hy hyS => by rw [hloc y hy hyS]⟩
  injective₀ x v hmem := by
    obtain ⟨v, hv⟩ := v
    have hv' := inv_mulVec_mem_of_mem_latticeMap hv
    have e1 : ((Q.u₁ x).comp (actBaseChange (locRing B x) h₀ (Q.L₁ x)).symm.toLinearMap)
        ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(latticeMap h₀ (Q.N₁ x)))) =
        Q.u₁ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨_, hv'⟩ : ↥(Q.N₁ x))) := by
      show Q.u₁ x ((actBaseChange (locRing B x) h₀ (Q.L₁ x)).symm ((1 : locRing B x) ⊗ₜ[𝒪] ⟨v, hv⟩)) = _
      rw [actBaseChange_symm_one_tmul]
    erw [e1] at hmem
    have hw := Q.injective₁ x ⟨_, hv'⟩ hmem
    refine ⟨(h₁ : Matrix (Fin 2) (Fin 2) K) *ᵥ ((((h₀⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v)),
      mulVec_mem_latticeMap hw, ?_⟩
    show v = algebraMap 𝒪 K π • ((h₁ : Matrix (Fin 2) (Fin 2) K) *ᵥ _)
    rw [← hh, mulVec_inv_mulVec]
  injective₁ x v hmem := by
    obtain ⟨v, hv⟩ := v
    have hv' := inv_mulVec_mem_of_mem_latticeMap hv
    have e1 : ((Q.u₀ x).comp (actBaseChange (locRing B x) h₁ (Q.L₀ x)).symm.toLinearMap)
        ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(latticeMap h₁ (Q.N₀ x)))) =
        Q.u₀ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨_, hv'⟩ : ↥(Q.N₀ x))) := by
      show Q.u₀ x ((actBaseChange (locRing B x) h₁ (Q.L₀ x)).symm ((1 : locRing B x) ⊗ₜ[𝒪] ⟨v, hv⟩)) = _
      rw [actBaseChange_symm_one_tmul]
    erw [e1] at hmem
    obtain ⟨w, hw, hvw⟩ := Q.injective₀ x ⟨_, hv'⟩ hmem
    show v ∈ latticeMap h₀ (Q.N₁ x)
    have : v = (h₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ w := by
      rw [hh, ← Matrix.mulVec_smul, ← hvw, mulVec_inv_mulVec]
    rw [this]
    exact mulVec_mem_latticeMap hw
  hasDetIndex₀ x hx := by
    have := hasDetIndex_latticeMap π hπK (Q.hasDetIndex₁ x hx) h₀ hdet₀
    norm_num at this
    exact this
  hasDetIndex₁ x hx := by
    have := hasDetIndex_latticeMap π hπK (Q.hasDetIndex₀ x hx) h₁ hdet₁
    norm_num at this
    exact this

end ReduceTE

namespace ReduceTE

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem val_det_scalarGL_mul (c : Kˣ) (m : Matrix.GeneralLinearGroup (Fin 2) K) :
    ((Matrix.GeneralLinearGroup.det (scalarGL c * m) : Kˣ) : K) = (c : K) ^ 2 * ((Matrix.GeneralLinearGroup.det m : Kˣ) : K) := by
  rw [map_mul, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, scalarGL_coe,
    Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]

theorem scalarGL_mul_mulVec_eq (g : Matrix.GeneralLinearGroup (Fin 2) K) (c₀ c₁ : Kˣ) (hc : (c₀ : K) = algebraMap 𝒪 K π * c₁)
    (v : Fin 2 → K) :
    ((scalarGL c₀ * g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v =
      algebraMap 𝒪 K π • (((scalarGL c₁ * g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v) := by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, scalarGL_mulVec, Units.val_mul, ← Matrix.mulVec_mulVec, scalarGL_mulVec, hc, mul_smul]

noncomputable def oddWitness (Q : DrinfeldDatum (K := K) π B) (g : Matrix.GeneralLinearGroup (Fin 2) K) (c₀ c₁ : Kˣ) (e : 𝒪ˣ)
    (hc : (c₀ : K) = algebraMap 𝒪 K π * c₁) (hπK : algebraMap 𝒪 K π ≠ 0)
    (hdet₀ : ((Matrix.GeneralLinearGroup.det (scalarGL c₀ * g⁻¹) : Kˣ) : K) = algebraMap 𝒪 K e * algebraMap 𝒪 K π ^ (1 : ℤ))
    (hdet₁ : ((Matrix.GeneralLinearGroup.det (scalarGL c₁ * g⁻¹) : Kˣ) : K) = algebraMap 𝒪 K e * algebraMap 𝒪 K π ^ (-1 : ℤ)) :
    DrinfeldDatum.TranslateOdd g c₀ c₁ Q
      (oddTranslate Q (scalarGL c₀ * g⁻¹) (scalarGL c₁ * g⁻¹) (scalarGL_mul_mulVec_eq g c₀ c₁ hc) hπK e hdet₀ hdet₁) where
  c₀_eq := hc
  N₀_eq x := rfl
  N₁_eq x := rfl
  σ₀ := LinearEquiv.refl B Q.T₁
  σ₁ := LinearEquiv.refl B Q.T₀
  σ₁_Pi₁ t := rfl
  σ₀_Pi₀ t := rfl
  σ₀_u₀ x v hv hv' := by
    have hid : ∀ y, LocalizedModule.map x.asIdeal.primeCompl (LinearEquiv.refl B Q.T₁).toLinearMap y = y := fun y => by
      rw [LinearEquiv.refl_toLinearMap]
      exact congrArg (fun F : LocalizedModule x.asIdeal.primeCompl Q.T₁ →ₗ[B] LocalizedModule x.asIdeal.primeCompl Q.T₁ => F y)
        (IsLocalizedModule.map_id x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl Q.T₁))
    refine Eq.trans ?_ (hid _).symm
    show Q.u₁ x ((actBaseChange (locRing B x) (scalarGL c₀ * g⁻¹) (Q.L₁ x)).symm ((1 : locRing B x) ⊗ₜ[𝒪] ⟨_, hv'⟩)) =
      Q.u₁ x ((1 : locRing B x) ⊗ₜ[𝒪] ⟨v, hv⟩)
    rw [actBaseChange_symm_one_tmul]
    congr 2
    exact Subtype.ext (inv_mulVec_mulVec _ v)
  σ₁_u₁ x v hv hv' := by
    have hid : ∀ y, LocalizedModule.map x.asIdeal.primeCompl (LinearEquiv.refl B Q.T₀).toLinearMap y = y := fun y => by
      rw [LinearEquiv.refl_toLinearMap]
      exact congrArg (fun F : LocalizedModule x.asIdeal.primeCompl Q.T₀ →ₗ[B] LocalizedModule x.asIdeal.primeCompl Q.T₀ => F y)
        (IsLocalizedModule.map_id x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl Q.T₀))
    refine Eq.trans ?_ (hid _).symm
    show Q.u₀ x ((actBaseChange (locRing B x) (scalarGL c₁ * g⁻¹) (Q.L₀ x)).symm ((1 : locRing B x) ⊗ₜ[𝒪] ⟨_, hv'⟩)) =
      Q.u₀ x ((1 : locRing B x) ⊗ₜ[𝒪] ⟨v, hv⟩)
    rw [actBaseChange_symm_one_tmul]
    congr 2
    exact Subtype.ext (inv_mulVec_mulVec _ v)

end ReduceTE

theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (Q : DrinfeldDatum (K := K) π B) (g : Matrix.GeneralLinearGroup (Fin 2) K) (c₀ c₁ : Kˣ) (e : 𝒪ˣ)
    (hc : (c₀ : K) = algebraMap 𝒪 K π * c₁)
    (hdet : algebraMap 𝒪 K π * ((Matrix.GeneralLinearGroup.det (scalarGL c₁ * g⁻¹) : Kˣ) : K) = algebraMap 𝒪 K e) :
    ∃ Q' : DrinfeldDatum (K := K) π B, Q.IsTranslateOdd g c₀ c₁ Q' := by
  have hπK : algebraMap 𝒪 K π ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdet
    exact (e.isUnit.map (algebraMap 𝒪 K)).ne_zero hdet.symm
  have hdet₁ : ((Matrix.GeneralLinearGroup.det (scalarGL c₁ * g⁻¹) : Kˣ) : K) = algebraMap 𝒪 K e * algebraMap 𝒪 K π ^ (-1 : ℤ) := by
    rw [zpow_neg_one, eq_mul_inv_iff_mul_eq₀ hπK, mul_comm]
    exact hdet
  have hdet₀ : ((Matrix.GeneralLinearGroup.det (scalarGL c₀ * g⁻¹) : Kˣ) : K) = algebraMap 𝒪 K e * algebraMap 𝒪 K π ^ (1 : ℤ) := by
    rw [zpow_one, ReduceTE.val_det_scalarGL_mul, hc, ← hdet, ReduceTE.val_det_scalarGL_mul]
    ring
  exact ⟨_, ⟨ReduceTE.oddWitness Q g c₀ c₁ e hc hπK hdet₀ hdet₁⟩⟩

#print axioms solution

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isTranslateOdd_of_det_mul_eq_algebraMap
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isTranslateOdd_of_det_mul_eq_algebraMap (solution)
