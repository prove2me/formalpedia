-- Prove2me | solution 1 for CohCarrier.exists_sigmaCorner_gammaZero_of_sigmaCorner_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/3612722b-efe7-5e80-b3ee-9ba39ea8a5a1

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CohCarrier_LevelPairing
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CohCarrier_Lower
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_LocalConditions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Theorems.Thm_CohCarrier_isUnit_index_of_forall_mem_iff_castHom_eq_one
import Theorems.Thm_CohCarrier_diamondL_mul_and_diamondL_one_and_diamondL_eq_one_of_mem
import Theorems.Thm_CohCarrier_injective_iDeg_one_and_range_eq_of_isUnit_index
import Theorems.Thm_CohCarrier_iDeg_diamondRaw_comm
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_coprime
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_dvd
import Theorems.Thm_IharaLemma_exists_pow_smul_corner_mem_maximalIdeal_smul
import Theorems.Thm_CohCarrier_HeckeData_finite_opSubalgebra_and_subsingleton_ML_or_exists_corner
import Theorems.Thm_CohCarrier_HeckeData_nonempty_idempotentSplitting_opSubalgebra
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Theorems.Thm_CohCarrier_opFamily_comm
import Theorems.Thm_IharaLemma_mem_cornerSubmodule_of_forall_exists_pow_sub_algebraMap_smul_mem
import Theorems.Thm_IharaLemma_finite_cornerSubmodule
import Theorems.Thm_IharaLemma_free_cornerSubmodule
import Definitions.Def_CohCarrier_HeckeData
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_sigmaCorner_gammaZero_of_sigmaCorner_gammaH

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open Polynomial IsLocalRing CohCarrier IharaLemma IharaTower

open scoped IsMulCommutative

namespace ExTop

open CongruenceSubgroup

theorem eq_one_of_pow_eq_one_of_sub_one_mem {C : Type} [CommRing C] [IsLocalRing C] (x : C) (n : ℕ)
    (hn : IsUnit ((n : ℕ) : C)) (hx : x ^ n = 1) (h1 : x - 1 ∈ IsLocalRing.maximalIdeal C) : x = 1 := by
  have hgeom : (x - 1) * (∑ k ∈ Finset.range n, x ^ k) = 0 := by
    rw [mul_comm, geom_sum_mul, hx, sub_self]
  have hmem : (∑ k ∈ Finset.range n, x ^ k) - (n : C) ∈ IsLocalRing.maximalIdeal C := by
    have : (∑ k ∈ Finset.range n, x ^ k) - (n : C) = ∑ k ∈ Finset.range n, (x ^ k - 1) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [this]
    refine Ideal.sum_mem _ fun k _ => ?_
    obtain ⟨c, hc⟩ := sub_one_dvd_pow_sub_one x k
    rw [hc]
    exact Ideal.mul_mem_right _ _ h1
  have hunit : IsUnit (∑ k ∈ Finset.range n, x ^ k) := by
    by_contra hnu
    have hmem' : (∑ k ∈ Finset.range n, x ^ k) ∈ IsLocalRing.maximalIdeal C :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have : (n : C) ∈ IsLocalRing.maximalIdeal C := by
      have := Ideal.sub_mem _ hmem' hmem
      rwa [sub_sub_cancel] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp this hn
  rw [mul_comm] at hgeom
  exact sub_eq_zero.mp (hunit.mul_right_eq_zero.mp hgeom)

theorem algebraMap_mem_of_mem_maximalIdeal {𝒪 B : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [CommRing B] [Algebra 𝒪 B]
    [Module.Finite 𝒪 B] (𝔪 : Ideal B) [𝔪.IsMaximal] {c : 𝒪} (hc : c ∈ IsLocalRing.maximalIdeal 𝒪) :
    algebraMap 𝒪 B c ∈ 𝔪 := by
  have hmax : (𝔪.comap (algebraMap 𝒪 B)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔪
  have heq : 𝔪.comap (algebraMap 𝒪 B) = IsLocalRing.maximalIdeal 𝒪 := IsLocalRing.eq_maximalIdeal hmax
  have : c ∈ 𝔪.comap (algebraMap 𝒪 B) := heq ▸ hc
  exact Ideal.mem_comap.mp this

theorem map_mem_pow_smul_top {𝒪 : Type} [CommRing 𝒪] {V W : Type} [AddCommGroup V] [Module 𝒪 V]
    [AddCommGroup W] [Module 𝒪 W] (f : V →ₗ[𝒪] W) (I : Ideal 𝒪) (k : ℕ) {v : V}
    (hv : v ∈ (I ^ k • ⊤ : Submodule 𝒪 V)) : f v ∈ (I ^ k • ⊤ : Submodule 𝒪 W) := by
  have h : (I ^ k • ⊤ : Submodule 𝒪 V).map f ≤ I ^ k • ⊤ := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact h ⟨v, hv, rfl⟩

theorem smul_mem_pow_smul_top {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module B V] [IsScalarTower 𝒪 B V]
    (I : Ideal 𝒪) (k : ℕ) (x : B) {v : V}
    (hv : v ∈ (I ^ k • ⊤ : Submodule 𝒪 V)) : x • v ∈ (I ^ k • ⊤ : Submodule 𝒪 V) :=
  map_mem_pow_smul_top ((DistribSMul.toLinearMap B V x).restrictScalars 𝒪) I k hv

theorem corner_smul_eq_zero_of_pow_smul_mem {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module B V] [IsScalarTower 𝒪 B V]
    (S : IdempotentSplitting B) (j : Fin S.n) (I : Ideal 𝒪)
    (hsep : ∀ v : V, (∀ k : ℕ, v ∈ (I ^ k • ⊤ : Submodule 𝒪 V)) → v = 0)
    (b : B) (hb : b ∉ S.𝔪 j) (w : V)
    (hw : ∀ k : ℕ, ∃ n : ℕ, (b ^ n) • w ∈ (I ^ k • ⊤ : Submodule 𝒪 V)) :
    S.e j • w = 0 := by
  obtain ⟨t, ht⟩ := exists_mul_mul_eq_of_notMem (S.idem j) (S.𝔪 j) (S.mem_of_isMaximal_of_ne j) hb
  have hpow : ∀ n : ℕ, (t * b) ^ n * S.e j = S.e j := by
    intro n
    induction n with
    | zero => rw [pow_zero, one_mul]
    | succ n ih => rw [pow_succ, mul_assoc, ht, ih]
  apply hsep
  intro k
  obtain ⟨n, hn⟩ := hw k
  rw [← hpow n, mul_pow, mul_right_comm, mul_smul]
  exact smul_mem_pow_smul_top I k _ hn

theorem mem_𝔪_of_pow_smul_mem {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module B V] [IsScalarTower 𝒪 B V]
    (S : IdempotentSplitting B) (j : Fin S.n) (I : Ideal 𝒪)
    (hsep : ∀ v : V, (∀ k : ℕ, v ∈ (I ^ k • ⊤ : Submodule 𝒪 V)) → v = 0)
    (w : V) (hw : S.e j • w ≠ 0) (b : B)
    (hb : ∀ k : ℕ, ∃ n : ℕ, (b ^ n) • w ∈ (I ^ k • ⊤ : Submodule 𝒪 V)) :
    b ∈ S.𝔪 j := by
  by_contra h
  exact hw (corner_smul_eq_zero_of_pow_smul_mem S j I hsep b h w hb)

theorem exists_corner_smul_ne_zero {B : Type} [CommRing B] {V : Type} [AddCommGroup V] [Module B V]
    (S : IdempotentSplitting B) (w : V) (hw : w ≠ 0) : ∃ j : Fin S.n, S.e j • w ≠ 0 := by
  by_contra h
  push_neg at h
  apply hw
  calc w = (∑ j, S.e j) • w := by rw [S.coi.complete, one_smul]
    _ = ∑ j, S.e j • w := Finset.sum_smul
    _ = 0 := Finset.sum_eq_zero (fun j _ => h j)

theorem isTorsionFree_addMonoidHom {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] (X : Type) [AddMonoid X] :
    Module.IsTorsionFree 𝒪 (X →+ 𝒪) := by
  refine Module.IsTorsionFree.of_smul_eq_zero (fun c f h => ?_)
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    ext x
    have := congrArg (fun g : X →+ 𝒪 => g x) h
    simp only [AddMonoidHom.smul_apply, AddMonoidHom.zero_apply, smul_eq_mul] at this
    exact (mul_eq_zero.mp this).resolve_left hc

theorem cornerRing_faithful {B : Type} [CommRing B] {V : Type} [AddCommGroup V] [Module B V]
    (S : IdempotentSplitting B) (i : Fin S.n) (hfaith : ∀ b : B, (∀ v : V, b • v = 0) → b = 0)
    (x : S.CornerRing i) (hx : ∀ m : ↥(cornerSubmodule (M := V) (S.e i)), x • m = 0) : x = 0 := by
  apply IdempotentSplitting.ext_cornerRing
  rw [IdempotentSplitting.coe_zero_cornerRing]
  apply hfaith
  intro v
  have h1 : (x : B) • v = (x : B) • (S.e i • v) := by
    rw [← mul_smul, IdempotentSplitting.coe_mul_e]
  have h2 := congrArg Subtype.val (hx ⟨S.e i • v, ⟨v, rfl⟩⟩)
  rw [h1]
  exact h2

theorem finite_and_free_of_submodule {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module B V] [IsScalarTower 𝒪 B V]
    [Module.Finite 𝒪 V] [Module.IsTorsionFree 𝒪 V] (W : Submodule B V) :
    Module.Finite 𝒪 ↥W ∧ Module.Free 𝒪 ↥W := by
  haveI : IsNoetherian 𝒪 V := isNoetherian_of_isNoetherianRing_of_finite 𝒪 V
  let incl : ↥W →ₗ[𝒪] V :=
    { toFun := fun m => (m : V), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  haveI hfin : Module.Finite 𝒪 ↥W := Module.Finite.of_injective incl Subtype.val_injective
  haveI : Module.IsTorsionFree 𝒪 ↥W :=
    Function.Injective.moduleIsTorsionFree incl Subtype.val_injective (map_smul incl)
  exact ⟨hfin, Module.free_of_finite_type_torsion_free' (R := 𝒪) (M := ↥W)⟩

theorem adjoin_eq_top_of_le {R A : Type} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A)
    (t : Set ↥S) (h : S ≤ Algebra.adjoin R (Subtype.val '' t)) : Algebra.adjoin R t = ⊤ := by
  apply Subalgebra.map_injective (f := S.val) Subtype.val_injective
  rw [Algebra.map_top, Subalgebra.range_val, AlgHom.map_adjoin]
  apply le_antisymm
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  · exact h

noncomputable def pickScalar {G B 𝒪 : Type} [Zero 𝒪] (P : G → Prop) (t : G → B) (c : G → 𝒪) : B → 𝒪 :=
  fun b => by classical exact if h : ∃ g, P g ∧ t g = b then c h.choose else 0

theorem pickScalar_spec {G B 𝒪 : Type} [Zero 𝒪] (P : G → Prop) (t : G → B) (c : G → 𝒪) (g : G)
    (hg : P g) : ∃ g', P g' ∧ t g' = t g ∧ pickScalar P t c (t g) = c g' := by
  classical
  have h : ∃ g', P g' ∧ t g' = t g := ⟨g, hg, rfl⟩
  refine ⟨h.choose, h.choose_spec.1, h.choose_spec.2, ?_⟩
  simp only [pickScalar, dif_pos h]

noncomputable def DT (S : Finset ℕ) (M L : ℕ) [NeZero L] (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (cfull : CohCarrier.Gen L (↑S : Set ℕ) → 𝒪) :
    CohCarrier.HeckeData 𝒪 (H1 L ⊤ 𝒪) (ResidueField 𝒪) where
  Gen := {g : CohCarrier.Gen L (↑S : Set ℕ) // ∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M}
  op := fun g => CohCarrier.opFamily L ⊤ (↑S : Set ℕ) 𝒪 g.1
  comm := fun g h => CohCarrier.opFamily_comm (↑S : Set ℕ) 𝒪 L ⊤ g.1 h.1
  θbar := fun g => IsLocalRing.residue 𝒪 (cfull g.1)

theorem DT_op (S : Finset ℕ) (M L : ℕ) [NeZero L] (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (cfull : CohCarrier.Gen L (↑S : Set ℕ) → 𝒪) (g : (DT S M L 𝒪 cfull).Gen) :
    (DT S M L 𝒪 cfull).op g = CohCarrier.opFamily L ⊤ (↑S : Set ℕ) 𝒪 g.1 := rfl

noncomputable def tF (S : Finset ℕ) (M L : ℕ) [NeZero L] (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (cfull : CohCarrier.Gen L (↑S : Set ℕ) → 𝒪) (g : CohCarrier.Gen L (↑S : Set ℕ)) :
    ↥(DT S M L 𝒪 cfull).opSubalgebra := by
  classical
  exact if h : (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) then
    ⟨CohCarrier.opFamily L ⊤ (↑S : Set ℕ) 𝒪 g, Algebra.subset_adjoin ⟨⟨g, h⟩, rfl⟩⟩ else 0

theorem tF_val (S : Finset ℕ) (M L : ℕ) [NeZero L] (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (cfull : CohCarrier.Gen L (↑S : Set ℕ) → 𝒪) (g : CohCarrier.Gen L (↑S : Set ℕ))
    (h : ∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) :
    (tF S M L 𝒪 cfull g : Module.End 𝒪 (H1 L ⊤ 𝒪)) = CohCarrier.opFamily L ⊤ (↑S : Set ℕ) 𝒪 g := by
  classical
  simp only [tF, dif_pos h]

end ExTop

open ExTop CongruenceSubgroup in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S)

    (M : ℕ) [NeZero M] (hMS : ∀ q : ℕ, q.Prime → q ∣ M → q ∈ S) (hMp : ¬ p ^ 2 ∣ M)
    (Smin : Finset ℕ) (hpSmin : p ∈ Smin) (hSmin : Smin ⊆ S)
    (hmin : ∀ q : ℕ, q.Prime → q ≠ p → (q ∈ Smin ↔ ¬ ρbar.IsUnramifiedAt q))
    (hMmin : ∀ q ∈ Smin, q ≠ p → q ∣ M)
    (hMunr : ∀ q : ℕ, q.Prime → q ≠ p → q ∉ Smin → q ∣ M → q ^ 2 ∣ M)
    (hM3 : ∀ q : ℕ, q.Prime → q ≠ p → q ^ 2 ∣ M → ¬ q ^ 3 ∣ M)
    (htame : ∀ q ∈ Smin, q ≠ p → (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)
    (hord : p ∣ M → (GaloisRepAdic.ofResidualGaloisRep ρbar).IsOrdinaryAt p)

    (r : ℕ) (hr : r.Prime) (hrS : r ∉ S) (hrM : ¬ r ∣ M) (hr1 : ¬ p ∣ r - 1)
    (hrρ : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime r →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ r →
        LinearMap.trace (ResidueField 𝒪) ρbar.V (ρbar.ρ σ) ^ 2 ≠ ((r : ResidueField 𝒪) + 1) ^ 2)

    [Fact (CuspForm.HasIntegralStructure M 2)]
    (θ : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓM hℓS)) * X + C (ℓ : ResidueField 𝒪))

    (L : ℕ) [NeZero L] (hL : L = M * r) (hrL : r ∣ L)
    (H : Subgroup (ZMod L)ˣ)
    (hH : ∀ v : (ZMod L)ˣ, v ∈ H ↔ ZMod.castHom hrL (ZMod r) (v : ZMod L) = 1)

    {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 L H 𝒪)] [IsScalarTower 𝒪 𝕋 (H1 L H 𝒪)]
    [Module.Finite 𝒪 𝕋]
    (Sp : IdempotentSplitting 𝕋) (i : Fin Sp.n)
    [Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 L H 𝒪) (Sp.e i))]
    [Module.Free 𝒪 ↥(cornerSubmodule (M := H1 L H 𝒪) (Sp.e i))]
    (tfull : CohCarrier.Gen L (↑S : Set ℕ) → 𝕋) (cfull : CohCarrier.Gen L (↑S : Set ℕ) → 𝒪)

    (hgen : ∀ x : 𝕋, ∃ f ∈ Algebra.adjoin 𝒪
        (CohCarrier.opFamily L H (↑S : Set ℕ) 𝒪 '' {g | (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M)}),
      ∀ m : H1 L H 𝒪, x • m = f m)
    (htfull : ∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      ∀ m : H1 L H 𝒪, tfull g • m = CohCarrier.opFamily L H (↑S : Set ℕ) 𝒪 g m)
    (hcfull : ∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      tfull g - algebraMap 𝒪 𝕋 (cfull g) ∈ Sp.𝔪 i)
    (hcofull : ∀ v : H1 L H 𝒪, (∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      ∀ k : ℕ, ∃ n : ℕ, ((tfull g - algebraMap 𝒪 𝕋 (cfull g)) ^ n) • v ∈
        ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 L H 𝒪))) →
      v ∈ cornerSubmodule (M := H1 L H 𝒪) (Sp.e i))

    (hcT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ L),
      IsLocalRing.residue 𝒪 (cfull (.T ℓ hℓ hℓS hℓL)) = θ (CuspForm.heckeAlgebra.T hℓ hℓM hℓS))
    (hcU0 : ∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), q ∣ M → q ≠ p → q ^ 2 ∣ M →
      cfull (.U q hq hqL) ∈ IsLocalRing.maximalIdeal 𝒪)
    (hcUp : ∀ (hpL : p ∣ L), p ∣ M → IsUnit (cfull (.U p Fact.out hpL)))
    (hcd : ∀ d : (ZMod L)ˣ, cfull (.dia d) - 1 ∈ IsLocalRing.maximalIdeal 𝒪)

    (hocc : cornerSubmodule (M := H1 L H 𝒪) (Sp.e i) ≠ ⊥)
    (hfaith : ∀ x : Sp.CornerRing i,
      (∀ m : ↥(cornerSubmodule (M := H1 L H 𝒪) (Sp.e i)), x • m = 0) → x = 0)

    (h₁ : LevelLE L L ⊤ H 1) :
    ∃ (𝕋' : Type) (_ : CommRing 𝕋') (_ : Algebra 𝒪 𝕋') (_ : Module 𝕋' (H1 L ⊤ 𝒪)) (_ : IsScalarTower 𝒪 𝕋' (H1 L ⊤ 𝒪))
      (_ : Module.Finite 𝒪 𝕋')
      (Sp' : IdempotentSplitting 𝕋') (i' : Fin Sp'.n)
      (_ : Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i')))
      (_ : Module.Free 𝒪 ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i')))
      (tfull' : CohCarrier.Gen L (↑S : Set ℕ) → 𝕋'),
      (∀ x : 𝕋', ∃ f ∈ Algebra.adjoin 𝒪
        (CohCarrier.opFamily L ⊤ (↑S : Set ℕ) 𝒪 '' {g | (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M)}),
        ∀ m : H1 L ⊤ 𝒪, x • m = f m) ∧
      (∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
        ∀ m : H1 L ⊤ 𝒪, tfull' g • m = CohCarrier.opFamily L ⊤ (↑S : Set ℕ) 𝒪 g m) ∧
      (∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
        tfull' g - algebraMap 𝒪 𝕋' (cfull g) ∈ Sp'.𝔪 i') ∧
      (∀ v : H1 L ⊤ 𝒪, (∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
        ∀ k : ℕ, ∃ n : ℕ, ((tfull' g - algebraMap 𝒪 𝕋' (cfull g)) ^ n) • v ∈
        ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 L ⊤ 𝒪))) →
        v ∈ cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i')) ∧
      (cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i') ≠ ⊥) ∧
      (∀ x : Sp'.CornerRing i',
        (∀ m : ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i')), x • m = 0) → x = 0) := by
  classical
  subst hL
  set V := H1 (M * r) ⊤ 𝒪 with hV

  have hguard_dia : ∀ d : (ZMod (M * r))ˣ, ∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ M * r),
      (CohCarrier.Gen.dia d : CohCarrier.Gen (M * r) (↑S : Set ℕ)) = CohCarrier.Gen.U q hq hqL → q ∣ M := by
    intro d q hq hqL h; cases h
  have hunit : IsUnit ((H.index : ℕ) : 𝒪) :=
    CohCarrier.isUnit_index_of_forall_mem_iff_castHom_eq_one p hp𝒪 M r hr hr1 H hH
  obtain ⟨-, hinj, hrange, hci⟩ :=
    CohCarrier.injective_iDeg_one_and_range_eq_of_isUnit_index (M * r) H 𝒪 𝒪 h₁ hunit
  set res := iDegL (M * r) (M * r) ⊤ H 1 𝒪 𝒪 h₁ with hres
  have hres_eq : ∀ a : H1 (M * r) ⊤ 𝒪, res a = iDeg' (M * r) (M * r) ⊤ H 1 𝒪 h₁ a := fun _ => rfl
  have hres_inj : Function.Injective res := fun a b h => hinj (by rw [← hres_eq, ← hres_eq]; exact h)
  have hconj1 : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h : ((1 : ℕ) : ℤ) ∣ A 1 0), conjLowerMat 1 A h = A := by
    intro A h
    apply Subtype.ext
    simp only [conjLowerMat]
    ext i' j'
    fin_cases i' <;> fin_cases j' <;> simp

  obtain ⟨hdmul, hdone, hdH⟩ := CohCarrier.diamondL_mul_and_diamondL_one_and_diamondL_eq_one_of_mem (M * r) H 𝒪
  have hdiam : ∀ σ : Gamma0 (M * r), ∀ v : H1 (M * r) H 𝒪,
      v ∈ cornerSubmodule (M := H1 (M * r) H 𝒪) (Sp.e i) → diamondRaw (M * r) H 𝒪 σ v = v := by
    intro σ v hv
    set d : (ZMod (M * r))ˣ := gamma0Units (M * r) σ with hd
    set t : 𝕋 := tfull (.dia d) with ht
    have hact : ∀ m : H1 (M * r) H 𝒪, t • m = diamondL (M * r) H 𝒪 d m := fun m =>
      htfull (.dia d) (hguard_dia d) m
    have hpow : ∀ m : H1 (M * r) H 𝒪, (t ^ H.index) • m = m := by
      intro m
      have key : ∀ k : ℕ, (t ^ k) • m = diamondL (M * r) H 𝒪 (d ^ k) m := by
        intro k
        induction k with
        | zero => rw [pow_zero, one_smul, pow_zero, hdone]; rfl
        | succ k ih => rw [pow_succ', mul_smul, ih, hact, pow_succ' d k, hdmul]; rfl
      rw [key, hdH _ (Subgroup.pow_index_mem H d)]; rfl
    set x : Sp.CornerRing i := Sp.toCornerRing i t with hx
    have hxpow : x ^ H.index = 1 := by
      refine sub_eq_zero.mp (hfaith _ fun m => ?_)
      have h1 : ((x ^ H.index - 1) • m : ↥(cornerSubmodule (M := H1 (M * r) H 𝒪) (Sp.e i))) =
          (x ^ H.index) • m - m := by
        have := sub_smul (x ^ H.index) (1 : Sp.CornerRing i) m
        rwa [one_smul] at this
      rw [h1, sub_eq_zero]
      apply Subtype.ext
      rw [IharaLemma.IdempotentSplitting.coe_cornerSmul, ← map_pow, IharaLemma.IdempotentSplitting.coe_toCornerRing,
        mul_comm (Sp.e i) (t ^ H.index), mul_assoc, (Sp.idem i).eq, mul_smul,
        IharaLemma.IdempotentSplitting.e_smul_coe, hpow]
    have hx1 : x - 1 ∈ IsLocalRing.maximalIdeal (Sp.CornerRing i) := by
      have hmem : t - 1 ∈ Sp.𝔪 i := by
        have h1 := hcfull (.dia d) (hguard_dia d)
        have h2 : algebraMap 𝒪 𝕋 (cfull (.dia d) - 1) ∈ Sp.𝔪 i :=
          algebraMap_mem_of_mem_maximalIdeal (Sp.𝔪 i) (hcd d)
        have : t - 1 = (t - algebraMap 𝒪 𝕋 (cfull (.dia d))) + algebraMap 𝒪 𝕋 (cfull (.dia d) - 1) := by
          rw [map_sub, map_one]; ring
        rw [this]; exact Ideal.add_mem _ h1 h2
      have : x - 1 = algebraMap 𝕋 (Sp.CornerRing i) (t - 1) := by
        rw [map_sub, map_one]; rfl
      rw [this]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Sp.CornerRing i) (Sp.𝔪 i) (t - 1)).mpr hmem
    have hxone : x = 1 :=
      eq_one_of_pow_eq_one_of_sub_one_mem x H.index (by simpa using hunit.map (algebraMap 𝒪 (Sp.CornerRing i)))
        hxpow hx1
    have hv1 : t • v = v := by
      have : ((x • ⟨v, hv⟩ : ↥(cornerSubmodule (M := H1 (M * r) H 𝒪) (Sp.e i))) : H1 (M * r) H 𝒪) = t • v := by
        rw [IharaLemma.IdempotentSplitting.coe_cornerSmul, IharaLemma.IdempotentSplitting.coe_toCornerRing,
          mul_comm (Sp.e i) t, mul_assoc, (Sp.idem i).eq, mul_smul]
        show t • (Sp.e i • v) = t • v
        rw [IharaLemma.IdempotentSplitting.e_smul_coe Sp i ⟨v, hv⟩]
      rw [← this, hxone, one_smul]
    rw [← diamondL_eq_diamondRaw (M * r) H 𝒪 d σ rfl v, ← hact, hv1]

  have hcommOp : ∀ g : CohCarrier.Gen (M * r) (↑S : Set ℕ),
      (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ M * r), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      ∀ a : V, res (CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 g a) = tfull g • res a := by
    intro g hg a
    rw [htfull g hg]
    cases g with
    | T ℓ hℓ hℓS hℓM =>
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      exact CohCarrier.iDeg_heckeT_comm_of_coprime h₁ (Nat.coprime_one_right ℓ) hℓ hℓM a
    | U q hq hqM =>
      haveI : NeZero q := ⟨hq.ne_zero⟩
      exact CohCarrier.iDeg_heckeT_comm_of_dvd h₁ (Nat.coprime_one_right q) hqM a
    | dia d =>
      obtain ⟨σ', hσ'⟩ := gamma0Units_surjective (M * r) d
      have hd1 : ((1 : ℕ) : ℤ) ∣ (σ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 := by simp
      show iDeg' (M * r) (M * r) ⊤ H 1 𝒪 h₁ (diamondL (M * r) ⊤ 𝒪 d a) = diamondL (M * r) H 𝒪 d (iDeg' (M * r) (M * r) ⊤ H 1 𝒪 h₁ a)
      rw [diamondL_eq_diamondRaw (M * r) ⊤ 𝒪 d σ' hσ' a, diamondL_eq_diamondRaw (M * r) H 𝒪 d σ' hσ']
      exact CohCarrier.iDeg_diamondRaw_comm h₁ σ' hd1 σ' (by rw [hconj1]) a
  have hcommOp_pow : ∀ g : CohCarrier.Gen (M * r) (↑S : Set ℕ),
      (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ M * r), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      ∀ (n : ℕ) (a : V),
        res (((CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 g - algebraMap 𝒪 _ (cfull g)) ^ n) a) =
          ((tfull g - algebraMap 𝒪 𝕋 (cfull g)) ^ n) • res a := by
    intro g hg n
    induction n with
    | zero => intro a; rw [pow_zero, pow_zero, one_smul, Module.End.one_apply]
    | succ n ih =>
      intro a
      rw [pow_succ', Module.End.mul_apply, pow_succ', mul_smul, ← ih]
      set b := ((CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 g - algebraMap 𝒪 _ (cfull g)) ^ n) a with hb
      rw [LinearMap.sub_apply, sub_smul, map_sub, hcommOp g hg b, algebraMap_smul 𝕋 (cfull g) (res b),
        Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply, LinearMap.map_smul]

  obtain ⟨u, hu⟩ := hunit
  have hpull : ∀ (k : ℕ) (a : V),
      res a ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 (M * r) H 𝒪)) →
        a ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 V) := by
    intro k a ha
    have hinv : ∀ σ : Gamma0 (M * r), diamondRaw (M * r) H 𝒪 σ (res a) = res a := by
      have : res a ∈ Set.range (iDeg' (M * r) (M * r) ⊤ H 1 𝒪 h₁) := ⟨a, rfl⟩
      rw [hrange] at this
      exact this
    have hcores : iDeg' (M * r) (M * r) ⊤ H 1 𝒪 h₁ (jDeg (M * r) (M * r) ⊤ H 1 𝒪 h₁ (res a)) =
        iDeg' (M * r) (M * r) ⊤ H 1 𝒪 h₁ ((H.index : 𝒪) • a) := by
      rw [hci _ hinv]
      show H.index • res a = res ((H.index : 𝒪) • a)
      rw [map_smul, Nat.cast_smul_eq_nsmul]
    have heq : jDegL (M * r) (M * r) ⊤ H 1 𝒪 𝒪 h₁ (res a) = (H.index : 𝒪) • a := hinj hcores
    have ha' : (H.index : 𝒪) • a ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 V) := by
      rw [← heq]
      exact map_mem_pow_smul_top _ _ k ha
    have : a = (↑u⁻¹ : 𝒪) • ((H.index : 𝒪) • a) := by
      rw [smul_smul, ← hu, Units.inv_mul, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ ha'

  haveI hVfin : Module.Finite 𝒪 V := CohCarrier.H1_moduleFinite (M * r) ⊤ 𝒪 𝒪
  have hsep : ∀ v' : V, (∀ k : ℕ, v' ∈ ((maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 V)) → v' = 0 := by
    intro v hv
    have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := V) (I := maximalIdeal 𝒪) (maximalIdeal.isMaximal 𝒪).ne_top
    have : v ∈ (⨅ k : ℕ, maximalIdeal 𝒪 ^ k • ⊤ : Submodule 𝒪 V) := (Submodule.mem_iInf _).mpr hv
    rwa [hK, Submodule.mem_bot] at this
  obtain ⟨v₀, hv₀, hv₀ne⟩ := (Submodule.ne_bot_iff _).mp hocc
  have hv₀r : v₀ ∈ Set.range (iDeg' (M * r) (M * r) ⊤ H 1 𝒪 h₁) := by
    rw [hrange]; exact fun σ => hdiam σ v₀ hv₀
  obtain ⟨a₀, ha₀⟩ := hv₀r
  have ha₀' : res a₀ = v₀ := ha₀
  have ha₀ne : a₀ ≠ 0 := by
    rintro rfl; exact hv₀ne (by rw [← ha₀', map_zero])
  have hnil : ∀ g : CohCarrier.Gen (M * r) (↑S : Set ℕ),
      (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ M * r), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      ∀ k : ℕ, ∃ n : ℕ, ((CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 g - algebraMap 𝒪 _ (cfull g)) ^ n) a₀ ∈
        ((maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 V) := by
    intro g hg k
    obtain ⟨n, hn⟩ := IharaLemma.exists_pow_smul_corner_mem_maximalIdeal_smul (𝒪 := 𝒪) Sp i
      (tfull g - algebraMap 𝒪 𝕋 (cfull g)) (hcfull g hg) (V := H1 (M * r) H 𝒪) k
    refine ⟨n, hpull k _ ?_⟩
    rw [hcommOp_pow g hg n a₀, ha₀']
    exact hn v₀ hv₀

  set D := DT S M (M * r) 𝒪 cfull with hD
  haveI hfin : Module.Finite 𝒪 ↥D.opSubalgebra :=
    (CohCarrier.HeckeData.finite_opSubalgebra_and_subsingleton_ML_or_exists_corner
      (IsLocalRing.residue_surjective) D).1
  obtain ⟨Sp'⟩ := CohCarrier.HeckeData.nonempty_idempotentSplitting_opSubalgebra D
  obtain ⟨i', hi'⟩ := exists_corner_smul_ne_zero Sp' a₀ ha₀ne

  have htF : ∀ g : CohCarrier.Gen (M * r) (↑S : Set ℕ),
      (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ M * r), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      ∀ m : V, tF S M (M * r) 𝒪 cfull g • m = CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 g m := by
    intro g hg m
    show (tF S M (M * r) 𝒪 cfull g : Module.End 𝒪 V) m = _
    rw [tF_val S M (M * r) 𝒪 cfull g hg]
  have htF_pow : ∀ g : CohCarrier.Gen (M * r) (↑S : Set ℕ),
      (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ M * r), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      ∀ (n : ℕ) (m : V), ((tF S M (M * r) 𝒪 cfull g - algebraMap 𝒪 _ (cfull g)) ^ n) • m =
        ((CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 g - algebraMap 𝒪 _ (cfull g)) ^ n) m := by
    intro g hg n m
    show (((tF S M (M * r) 𝒪 cfull g - algebraMap 𝒪 _ (cfull g)) ^ n : ↥D.opSubalgebra) : Module.End 𝒪 V) m = _
    congr 1
    rw [SubmonoidClass.coe_pow, AddSubgroupClass.coe_sub, tF_val S M (M * r) 𝒪 cfull g hg]
    rfl

  have hcF : ∀ g : CohCarrier.Gen (M * r) (↑S : Set ℕ),
      (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ M * r), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      tF S M (M * r) 𝒪 cfull g - algebraMap 𝒪 _ (cfull g) ∈ Sp'.𝔪 i' := by
    intro g hg
    refine mem_𝔪_of_pow_smul_mem Sp' i' (maximalIdeal 𝒪) hsep a₀ hi' _ fun k => ?_
    obtain ⟨n, hn⟩ := hnil g hg k
    exact ⟨n, by rw [htF_pow g hg n a₀]; exact hn⟩

  haveI : Module.IsTorsionFree 𝒪 V := isTorsionFree_addMonoidHom (Additive ↥(GammaH (M * r) ⊤))
  obtain ⟨hfinC, hfreeC⟩ := finite_and_free_of_submodule (𝒪 := 𝒪) (cornerSubmodule (M := V) (Sp'.e i'))
  have hfaithB : ∀ b : ↥D.opSubalgebra, (∀ v : V, b • v = 0) → b = 0 := fun b hb =>
    Subtype.ext (LinearMap.ext hb)

  set G : Set (CohCarrier.Gen (M * r) (↑S : Set ℕ)) :=
    {g | ∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ M * r), g = CohCarrier.Gen.U q hq hqL → q ∣ M} with hG
  have hrangeOp : Set.range D.op = CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 '' G := by
    ext f
    constructor
    · rintro ⟨g, rfl⟩; exact ⟨g.1, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩; exact ⟨⟨g, hg⟩, rfl⟩
  have hGtop : Algebra.adjoin 𝒪 (tF S M (M * r) 𝒪 cfull '' G) = (⊤ : Subalgebra 𝒪 ↥D.opSubalgebra) := by
    refine adjoin_eq_top_of_le _ _ ?_
    show Algebra.adjoin 𝒪 (Set.range D.op) ≤ _
    rw [hrangeOp]
    refine Algebra.adjoin_mono ?_
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨tF S M (M * r) 𝒪 cfull g, ⟨g, hg, rfl⟩, tF_val S M (M * r) 𝒪 cfull g hg⟩
  refine ⟨↥D.opSubalgebra, inferInstance, inferInstance, inferInstance, inferInstance, hfin, Sp', i', hfinC, hfreeC,
    tF S M (M * r) 𝒪 cfull, fun x => ?_, htF, hcF, fun v hv => ?_, ?_, fun x hx => cornerRing_faithful Sp' i' hfaithB x hx⟩
  ·
    refine ⟨(x : Module.End 𝒪 V), ?_, fun m => rfl⟩
    have hx2 : (x : Module.End 𝒪 V) ∈ D.opSubalgebra := x.2
    change (x : Module.End 𝒪 V) ∈ Algebra.adjoin 𝒪 (Set.range D.op) at hx2
    rwa [hrangeOp] at hx2
  ·
    refine IharaLemma.mem_cornerSubmodule_of_forall_exists_pow_sub_algebraMap_smul_mem (𝒪 := 𝒪) hsep Sp' i'
      (tF S M (M * r) 𝒪 cfull '' G) hGtop (pickScalar (fun g => g ∈ G) (tF S M (M * r) 𝒪 cfull) cfull) ?_ v ?_
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨g', hg', htg', hc'⟩ := pickScalar_spec (fun g => g ∈ G) (tF S M (M * r) 𝒪 cfull) cfull g hg
      rw [hc', ← htg']
      exact hcF g' hg'
    · rintro _ ⟨g, hg, rfl⟩ k
      obtain ⟨g', hg', htg', hc'⟩ := pickScalar_spec (fun g => g ∈ G) (tF S M (M * r) 𝒪 cfull) cfull g hg
      rw [hc', ← htg']
      exact hv g' hg' k
  ·
    intro hbot
    apply hi'
    have : Sp'.e i' • a₀ ∈ cornerSubmodule (M := V) (Sp'.e i') := ⟨a₀, rfl⟩
    rw [hbot, Submodule.mem_bot] at this
    exact this

end S_CohCarrier_exists_sigmaCorner_gammaZero_of_sigmaCorner_gammaH
end P2MW
export P2MW.S_CohCarrier_exists_sigmaCorner_gammaZero_of_sigmaCorner_gammaH (solution)
