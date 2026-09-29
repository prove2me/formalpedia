-- Prove2me | solution 1 for CuspForm.heckeLocal.finrank_le_of_forall_point_exists_extension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/cb9e1fca-5b1f-56be-b2c0-98edfec8f895

import Theorems.Thm_IsLocalRing_exists_fin_points_dvr_iInf_ker_eq_bot
import Theorems.Thm_CuspForm_isReduced_heckeLocal_of_primeFactors_subset
import Theorems.Thm_CuspForm_heckeLocal_residue_pi
import Theorems.Thm_CuspForm_heckeLocal_adjoin_range_pi
import Theorems.Thm_CuspForm_heckeLocal_exists_factor_algHom
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeLocal_finrank_le_of_forall_point_exists_extension

set_option autoImplicit false

noncomputable section

namespace K1RL

open IsLocalRing CuspForm

theorem map_mem_maximalIdeal {R T : Type} [CommRing R] [IsLocalRing R] [CommRing T]
    [IsLocalRing T] (f : R →+* T) [IsLocalHom f] {x : R} (hx : x ∈ maximalIdeal R) :
    f x ∈ maximalIdeal T :=
  fun hu => hx (IsUnit.of_map f x hu)

theorem algebraMap_injective_of_charZero
    {𝒪 A : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [Finite (ResidueField 𝒪)]
    [CommRing A] [IsDomain A] [CharZero A] [Algebra 𝒪 A] :
    Function.Injective (algebraMap 𝒪 A) := by
  classical
  obtain ⟨q, hqchar⟩ := CharP.exists (ResidueField 𝒪)
  haveI := hqchar
  have hq : q.Prime := CharP.char_is_prime (ResidueField 𝒪) q
  have hqm : (q : 𝒪) ∈ maximalIdeal 𝒪 := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero (ResidueField 𝒪) q
  rw [RingHom.injective_iff_ker_eq_bot]
  set 𝔭 := RingHom.ker (algebraMap 𝒪 A) with h𝔭
  haveI h𝔭prime : 𝔭.IsPrime := RingHom.ker_isPrime _
  have hq𝔭 : (q : 𝒪) ∉ 𝔭 := by
    intro h
    rw [h𝔭, RingHom.mem_ker, map_natCast] at h
    exact hq.ne_zero (Nat.cast_eq_zero.mp h)
  by_contra hne
  have hmax : 𝔭 = maximalIdeal 𝒪 := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
    obtain ⟨m, hm⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
    have hϖmem : ϖ ∈ 𝔭 := by
      have hpow : ϖ ^ m ∈ 𝔭 := hm ▸ Ideal.mem_span_singleton_self _
      exact h𝔭prime.mem_of_pow_mem m hpow
    apply le_antisymm (IsLocalRing.le_maximalIdeal h𝔭prime.ne_top)
    rw [hϖ.maximalIdeal_eq, Ideal.span_le, Set.singleton_subset_iff]
    exact hϖmem
  exact hq𝔭 (hmax ▸ hqm)

theorem residue_comp_pi (N : ℕ) [NeZero N] (S : Set ℕ)
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    [Fact (HasIntegralStructure N 2)]
    (θ : heckeAlgebra N 2 S →+* ResidueField 𝒪)
    {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    (χ : heckeLocal N S 𝒪 θ →ₐ[𝒪] A) (hχ : IsLocalHom χ.toRingHom)
    (t : heckeAlgebra N 2 S) :
    residue A (χ (heckeLocal.π N S 𝒪 θ t)) = ResidueField.map (algebraMap 𝒪 A) (θ t) := by
  set T : Type := heckeLocal N S 𝒪 θ
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (θ t)
  have hπ : residue T (heckeLocal.π N S 𝒪 θ t) = residue T (algebraMap 𝒪 T a) := by
    rw [heckeLocal.residue_pi N S 𝒪 θ t, ← ha, IsLocalRing.ResidueField.map_residue]
  have hmem : heckeLocal.π N S 𝒪 θ t - algebraMap 𝒪 T a ∈ maximalIdeal T := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact hπ
  have hmem' : χ (heckeLocal.π N S 𝒪 θ t) - algebraMap 𝒪 A a ∈ maximalIdeal A := by
    haveI := hχ
    have h2 := map_mem_maximalIdeal χ.toRingHom hmem
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, AlgHom.commutes] at h2
    exact h2
  rw [← ha, IsLocalRing.ResidueField.map_residue, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff]
  exact hmem'

theorem main
    (N : ℕ) [NeZero N] (S S₀ : Set ℕ) (hS₀ : S₀ ⊆ S)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
    (θ' : CuspForm.heckeAlgebra N 2 S₀ →+* ResidueField 𝒪)
    (hlift : ∀ (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
        [IsAdicComplete (maximalIdeal 𝒪') 𝒪'] [Finite (ResidueField 𝒪')] [CharZero 𝒪']
        [Algebra 𝒪 𝒪'] [Module.Finite 𝒪 𝒪'] [IsLocalHom (algebraMap 𝒪 𝒪')],
        Function.Injective (algebraMap 𝒪 𝒪') →
      ∀ χ : CuspForm.heckeAlgebra N 2 S →+* 𝒪',
        (∀ t, residue 𝒪' (χ t) = ResidueField.map (algebraMap 𝒪 𝒪') (θ t)) →
        ∃ (𝒪'' : Type) (_ : CommRing 𝒪'') (_ : IsDomain 𝒪'') (_ : IsDiscreteValuationRing 𝒪'')
          (_ : IsAdicComplete (maximalIdeal 𝒪'') 𝒪'') (_ : Finite (ResidueField 𝒪''))
          (_ : CharZero 𝒪'') (_ : Algebra 𝒪' 𝒪'') (_ : Module.Finite 𝒪' 𝒪'')
          (_ : IsLocalHom (algebraMap 𝒪' 𝒪'')),
        Function.Injective (algebraMap 𝒪' 𝒪'') ∧
        ∃ χ' : CuspForm.heckeAlgebra N 2 S₀ →+* 𝒪'',
          (∀ t : CuspForm.heckeAlgebra N 2 S,
            χ' (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono hS₀) t) =
              algebraMap 𝒪' 𝒪'' (χ t)) ∧
          ∀ t : CuspForm.heckeAlgebra N 2 S₀, residue 𝒪'' (χ' t) =
            ResidueField.map (algebraMap 𝒪' 𝒪'') (ResidueField.map (algebraMap 𝒪 𝒪') (θ' t))) :
    Module.finrank 𝒪 (CuspForm.heckeLocal N S 𝒪 θ) ≤
      Module.finrank 𝒪 (CuspForm.heckeLocal N S₀ 𝒪 θ') := by
  classical
  have hint : HasIntegralStructure N 2 := Fact.out
  set T : Type := heckeLocal N S 𝒪 θ with hTdef
  set T' : Type := heckeLocal N S₀ 𝒪 θ' with hT'def

  haveI : IsReduced T := isReduced_heckeLocal_of_primeFactors_subset N S hNS 𝒪 θ

  obtain ⟨n, A, _, _, _, _, _, _, _, _, hAloc, χ, hχloc, hker, -⟩ :=
    IsLocalRing.exists_fin_points_dvr_iInf_ker_eq_bot (𝒪 := 𝒪) (P := T)
  haveI : ∀ i, IsLocalHom (algebraMap 𝒪 (A i)) := hAloc

  have hinjA : ∀ i, Function.Injective (algebraMap 𝒪 (A i)) := fun i =>
    algebraMap_injective_of_charZero
  have hred : ∀ i, ∀ t, residue (A i) ((χ i).toRingHom.comp (heckeLocal.π N S 𝒪 θ) t) =
      ResidueField.map (algebraMap 𝒪 (A i)) (θ t) := fun i t =>
    residue_comp_pi N S θ (χ i) (hχloc i) t
  have key := fun i => hlift (A i) (hinjA i) ((χ i).toRingHom.comp (heckeLocal.π N S 𝒪 θ)) (hred i)
  choose B iCR iDom iDVR iCpl iFin iCZ iAlg iMF iLH hinjB χ' hχ'ext hχ'red using key

  letI algOB : ∀ i, Algebra 𝒪 (B i) := fun i =>
    ((algebraMap (A i) (B i)).comp (algebraMap 𝒪 (A i))).toAlgebra
  haveI towOB : ∀ i, IsScalarTower 𝒪 (A i) (B i) := fun i =>
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI locOB : ∀ i, IsLocalHom (algebraMap 𝒪 (B i)) := fun i => by
    rw [IsScalarTower.algebraMap_eq 𝒪 (A i) (B i)]
    exact RingHom.isLocalHom_comp _ _

  have hfac : ∀ i, ∃ ψ : T' →ₐ[𝒪] B i, ∀ t, ψ (heckeLocal.π N S₀ 𝒪 θ' t) = χ' i t := by
    intro i
    have hπ' : ∀ t, residue (B i) (χ' i t) = ResidueField.map (algebraMap 𝒪 (B i)) (θ' t) := by
      intro t
      rw [hχ'red i t, IsLocalRing.ResidueField.map_map]
      rfl
    obtain ⟨ψ, -, hψ⟩ := heckeLocal.exists_factor_algHom N S₀ 𝒪 θ' hint (B i) (χ' i) hπ'
    exact ⟨ψ, hψ⟩
  choose ψ hψ using hfac

  set Χ : T →ₐ[𝒪] (∀ i, A i) := Pi.algHom 𝒪 A χ with hΧdef
  set ι : (∀ i, A i) →ₐ[𝒪] (∀ i, B i) :=
    Pi.algHom 𝒪 B (fun i => (IsScalarTower.toAlgHom 𝒪 (A i) (B i)).comp (Pi.evalAlgHom 𝒪 A i))
    with hιdef
  set Φ : T' →ₐ[𝒪] (∀ i, B i) := Pi.algHom 𝒪 B ψ with hΦdef
  have hΧinj : Function.Injective Χ := by
    intro x y hxy
    rw [← sub_eq_zero]
    have hmem : x - y ∈ (⨅ i, RingHom.ker (χ i).toRingHom) := by
      refine Ideal.mem_iInf.mpr fun i => ?_
      rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, sub_eq_zero]
      exact congrFun hxy i
    rw [hker] at hmem
    exact (Submodule.mem_bot _).mp hmem
  have hιinj : Function.Injective ι := by
    intro x y hxy
    funext i
    exact hinjB i (congrFun hxy i)

  have hgen : ∀ t : heckeAlgebra N 2 S,
      ι (Χ (heckeLocal.π N S 𝒪 θ t)) =
        Φ (heckeLocal.π N S₀ 𝒪 θ' (Subalgebra.inclusion (heckeAlgebra_mono hS₀) t)) := by
    intro t
    funext i
    change algebraMap (A i) (B i) (χ i (heckeLocal.π N S 𝒪 θ t)) =
      ψ i (heckeLocal.π N S₀ 𝒪 θ' (Subalgebra.inclusion (heckeAlgebra_mono hS₀) t))
    rw [hψ i, hχ'ext i t]
    rfl
  have hrange : (ι.comp Χ).range ≤ Φ.range := by
    have htop : (ι.comp Χ).range = Subalgebra.map (ι.comp Χ) ⊤ := Algebra.map_top _ |>.symm
    rw [htop, ← heckeLocal.adjoin_range_pi N S 𝒪 θ hint, AlgHom.map_adjoin, Algebra.adjoin_le_iff]
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨_, (hgen t).symm⟩

  have h1 : Module.finrank 𝒪 T = Module.finrank 𝒪 (LinearMap.range (ι.comp Χ).toLinearMap) :=
    (LinearMap.finrank_range_of_inj (f := (ι.comp Χ).toLinearMap) (hιinj.comp hΧinj)).symm
  have h2 : LinearMap.range (ι.comp Χ).toLinearMap ≤ LinearMap.range Φ.toLinearMap := by
    intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    obtain ⟨z, hz⟩ := (AlgHom.mem_range _).mp (hrange ((AlgHom.mem_range _).mpr ⟨y, rfl⟩))
    exact LinearMap.mem_range.mpr ⟨z, hz⟩
  calc Module.finrank 𝒪 T
      = Module.finrank 𝒪 (LinearMap.range (ι.comp Χ).toLinearMap) := h1
    _ ≤ Module.finrank 𝒪 (LinearMap.range Φ.toLinearMap) := Submodule.finrank_mono h2
    _ ≤ Module.finrank 𝒪 T' := LinearMap.finrank_range_le Φ.toLinearMap

end K1RL

end

open IsLocalRing in
theorem solution
    (N : ℕ) [NeZero N] (S S₀ : Set ℕ) (hS₀ : S₀ ⊆ S)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
    (θ' : CuspForm.heckeAlgebra N 2 S₀ →+* ResidueField 𝒪)
    (hlift : ∀ (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
        [IsAdicComplete (maximalIdeal 𝒪') 𝒪'] [Finite (ResidueField 𝒪')] [CharZero 𝒪']
        [Algebra 𝒪 𝒪'] [Module.Finite 𝒪 𝒪'] [IsLocalHom (algebraMap 𝒪 𝒪')],
        Function.Injective (algebraMap 𝒪 𝒪') →
      ∀ χ : CuspForm.heckeAlgebra N 2 S →+* 𝒪',
        (∀ t, residue 𝒪' (χ t) = ResidueField.map (algebraMap 𝒪 𝒪') (θ t)) →
        ∃ (𝒪'' : Type) (_ : CommRing 𝒪'') (_ : IsDomain 𝒪'') (_ : IsDiscreteValuationRing 𝒪'')
          (_ : IsAdicComplete (maximalIdeal 𝒪'') 𝒪'') (_ : Finite (ResidueField 𝒪''))
          (_ : CharZero 𝒪'') (_ : Algebra 𝒪' 𝒪'') (_ : Module.Finite 𝒪' 𝒪'')
          (_ : IsLocalHom (algebraMap 𝒪' 𝒪'')),
        Function.Injective (algebraMap 𝒪' 𝒪'') ∧
        ∃ χ' : CuspForm.heckeAlgebra N 2 S₀ →+* 𝒪'',
          (∀ t : CuspForm.heckeAlgebra N 2 S,
            χ' (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono hS₀) t) =
              algebraMap 𝒪' 𝒪'' (χ t)) ∧
          ∀ t : CuspForm.heckeAlgebra N 2 S₀, residue 𝒪'' (χ' t) =
            ResidueField.map (algebraMap 𝒪' 𝒪'') (ResidueField.map (algebraMap 𝒪 𝒪') (θ' t))) :
    Module.finrank 𝒪 (CuspForm.heckeLocal N S 𝒪 θ) ≤
      Module.finrank 𝒪 (CuspForm.heckeLocal N S₀ 𝒪 θ') :=
  K1RL.main N S S₀ hS₀ hNS 𝒪 θ θ' hlift

end S_CuspForm_heckeLocal_finrank_le_of_forall_point_exists_extension
end P2MW
export P2MW.S_CuspForm_heckeLocal_finrank_le_of_forall_point_exists_extension (solution)
