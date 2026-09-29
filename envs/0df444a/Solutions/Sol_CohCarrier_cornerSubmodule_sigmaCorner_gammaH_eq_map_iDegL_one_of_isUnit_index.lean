-- Prove2me | solution 1 for CohCarrier.cornerSubmodule_sigmaCorner_gammaH_eq_map_iDegL_one_of_isUnit_index
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/ae285d67-2f11-593b-b7e3-6e4db8c93e23

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
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_cornerSubmodule_sigmaCorner_gammaH_eq_map_iDegL_one_of_isUnit_index

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open Polynomial IsLocalRing CohCarrier IharaLemma IharaTower

namespace DDesc

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

end DDesc

open DDesc CongruenceSubgroup in
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

    {𝕋' : Type} [CommRing 𝕋'] [Algebra 𝒪 𝕋'] [Module 𝕋' (H1 L ⊤ 𝒪)] [IsScalarTower 𝒪 𝕋' (H1 L ⊤ 𝒪)]
    [Module.Finite 𝒪 𝕋']
    (Sp' : IdempotentSplitting 𝕋') (i' : Fin Sp'.n)
    [Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i'))]
    [Module.Free 𝒪 ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i'))]
    (tfull' : CohCarrier.Gen L (↑S : Set ℕ) → 𝕋')

    (hgen' : ∀ x : 𝕋', ∃ f ∈ Algebra.adjoin 𝒪
        (CohCarrier.opFamily L ⊤ (↑S : Set ℕ) 𝒪 '' {g | (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M)}),
      ∀ m : H1 L ⊤ 𝒪, x • m = f m)
    (htfull' : ∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      ∀ m : H1 L ⊤ 𝒪, tfull' g • m = CohCarrier.opFamily L ⊤ (↑S : Set ℕ) 𝒪 g m)
    (hcfull' : ∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      tfull' g - algebraMap 𝒪 𝕋' (cfull g) ∈ Sp'.𝔪 i')
    (hcofull' : ∀ v : H1 L ⊤ 𝒪, (∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      ∀ k : ℕ, ∃ n : ℕ, ((tfull' g - algebraMap 𝒪 𝕋' (cfull g)) ^ n) • v ∈
        ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 L ⊤ 𝒪))) →
      v ∈ cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i'))

    (hocc' : cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i') ≠ ⊥)
    (hfaith' : ∀ x : Sp'.CornerRing i',
      (∀ m : ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i')), x • m = 0) → x = 0)

    (h₁ : LevelLE L L ⊤ H 1) :

    (∀ v : H1 L H 𝒪, v ∈ cornerSubmodule (M := H1 L H 𝒪) (Sp.e i) ↔
      ∃ a : H1 L ⊤ 𝒪, a ∈ cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i') ∧ v = iDegL L L ⊤ H 1 𝒪 𝒪 h₁ a) ∧
    (∀ a : H1 L ⊤ 𝒪, a ∈ cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i') → iDegL L L ⊤ H 1 𝒪 𝒪 h₁ a = 0 → a = 0) ∧

    Module.finrank 𝒪 ↥(cornerSubmodule (M := H1 L H 𝒪) (Sp.e i)) =
      Module.finrank 𝒪 ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i')) ∧

    ∃ eD : Sp.CornerRing i ≃ₐ[𝒪] Sp'.CornerRing i',
      (∀ g : CohCarrier.Gen L (↑S : Set ℕ), (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
        eD (Sp.toCornerRing i (tfull g)) = Sp'.toCornerRing i' (tfull' g)) ∧
      (∀ (x : Sp.CornerRing i) (a : ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i')))
          (v : ↥(cornerSubmodule (M := H1 L H 𝒪) (Sp.e i))),
        (v : H1 L H 𝒪) = iDegL L L ⊤ H 1 𝒪 𝒪 h₁ (a : H1 L ⊤ 𝒪) →
          ((x • v : ↥(cornerSubmodule (M := H1 L H 𝒪) (Sp.e i))) : H1 L H 𝒪) =
            iDegL L L ⊤ H 1 𝒪 𝒪 h₁ ((eD x • a : ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i'))) : H1 L ⊤ 𝒪)) := by
  classical
  subst hL
  have hguard_dia : ∀ d : (ZMod (M * r))ˣ, ∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ M * r),
      (CohCarrier.Gen.dia d : CohCarrier.Gen (M * r) (↑S : Set ℕ)) = CohCarrier.Gen.U q hq hqL → q ∣ M := by
    intro d q hq hqL h; cases h
  have hunit : IsUnit ((H.index : ℕ) : 𝒪) :=
    CohCarrier.isUnit_index_of_forall_mem_iff_castHom_eq_one p hp𝒪 M r hr hr1 H hH
  obtain ⟨-, hinj, hrange, hci⟩ :=
    CohCarrier.injective_iDeg_one_and_range_eq_of_isUnit_index (M * r) H 𝒪 𝒪 h₁ hunit
  have hres_eq : ∀ a : H1 (M * r) ⊤ 𝒪, iDegL (M * r) (M * r) ⊤ H 1 𝒪 𝒪 h₁ a = iDeg' (M * r) (M * r) ⊤ H 1 𝒪 h₁ a :=
    fun _ => rfl

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

  set res := iDegL (M * r) (M * r) ⊤ H 1 𝒪 𝒪 h₁ with hres
  have hres_inj : Function.Injective res := fun a b h => hinj (by rw [← hres_eq, ← hres_eq]; exact h)

  have hconj1 : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h : ((1 : ℕ) : ℤ) ∣ A 1 0), conjLowerMat 1 A h = A := by
    intro A h
    apply Subtype.ext
    simp only [conjLowerMat]
    ext i' j'
    fin_cases i' <;> fin_cases j' <;> simp

  have hcomm : ∀ g : CohCarrier.Gen (M * r) (↑S : Set ℕ),
      (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ M * r), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      ∀ a : H1 (M * r) ⊤ 𝒪, res (tfull' g • a) = tfull g • res a := by
    intro g hg a
    rw [htfull' g hg, htfull g hg]
    cases g with
    | T ℓ hℓ hℓS hℓM =>
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      show iDeg' (M * r) (M * r) ⊤ H 1 𝒪 h₁ (heckeT (M * r) ⊤ ℓ 𝒪 a) = heckeT (M * r) H ℓ 𝒪 (iDeg' (M * r) (M * r) ⊤ H 1 𝒪 h₁ a)
      exact CohCarrier.iDeg_heckeT_comm_of_coprime h₁ (Nat.coprime_one_right ℓ) hℓ hℓM a
    | U q hq hqM =>
      haveI : NeZero q := ⟨hq.ne_zero⟩
      show iDeg' (M * r) (M * r) ⊤ H 1 𝒪 h₁ (heckeT (M * r) ⊤ q 𝒪 a) = heckeT (M * r) H q 𝒪 (iDeg' (M * r) (M * r) ⊤ H 1 𝒪 h₁ a)
      exact CohCarrier.iDeg_heckeT_comm_of_dvd h₁ (Nat.coprime_one_right q) hqM a
    | dia d =>
      obtain ⟨σ', hσ'⟩ := gamma0Units_surjective (M * r) d
      have hd1 : ((1 : ℕ) : ℤ) ∣ (σ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 := by simp
      show iDeg' (M * r) (M * r) ⊤ H 1 𝒪 h₁ (diamondL (M * r) ⊤ 𝒪 d a) = diamondL (M * r) H 𝒪 d (iDeg' (M * r) (M * r) ⊤ H 1 𝒪 h₁ a)
      rw [diamondL_eq_diamondRaw (M * r) ⊤ 𝒪 d σ' hσ' a, diamondL_eq_diamondRaw (M * r) H 𝒪 d σ' hσ']
      exact CohCarrier.iDeg_diamondRaw_comm h₁ σ' hd1 σ' (by rw [hconj1]) a

  have hcomm_pow : ∀ g : CohCarrier.Gen (M * r) (↑S : Set ℕ),
      (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ M * r), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      ∀ (n : ℕ) (a : H1 (M * r) ⊤ 𝒪),
        res (((tfull' g - algebraMap 𝒪 𝕋' (cfull g)) ^ n) • a) = ((tfull g - algebraMap 𝒪 𝕋 (cfull g)) ^ n) • res a := by
    intro g hg n
    induction n with
    | zero => intro a; rw [pow_zero, pow_zero, one_smul, one_smul]
    | succ n ih =>
      intro a
      rw [pow_succ', mul_smul, pow_succ', mul_smul, ← ih]
      set b := ((tfull' g - algebraMap 𝒪 𝕋' (cfull g)) ^ n) • a with hb
      rw [sub_smul, sub_smul, map_sub, hcomm g hg b, algebraMap_smul 𝕋' (cfull g) b,
        algebraMap_smul 𝕋 (cfull g) (res b), LinearMap.map_smul]

  obtain ⟨u, hu⟩ := hunit
  have hpull : ∀ (k : ℕ) (a : H1 (M * r) ⊤ 𝒪),
      res a ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 (M * r) H 𝒪)) →
        a ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 (M * r) ⊤ 𝒪)) := by
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
    have ha' : (H.index : 𝒪) • a ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 (M * r) ⊤ 𝒪)) := by
      rw [← heq]
      have hmap : ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 (M * r) H 𝒪)).map
          (jDegL (M * r) (M * r) ⊤ H 1 𝒪 𝒪 h₁) ≤ (IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ := by
        rw [Submodule.map_smul'']
        exact Submodule.smul_mono le_rfl le_top
      exact hmap ⟨res a, ha, rfl⟩
    have : a = (↑u⁻¹ : 𝒪) • ((H.index : 𝒪) • a) := by
      rw [smul_smul, ← hu, Units.inv_mul, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ ha'
  have hpush : ∀ (k : ℕ) (a : H1 (M * r) ⊤ 𝒪),
      a ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 (M * r) ⊤ 𝒪)) →
        res a ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 (M * r) H 𝒪)) := by
    intro k a ha
    have hmap : ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 (M * r) ⊤ 𝒪)).map res ≤
        (IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact hmap ⟨a, ha, rfl⟩

  have hfwd : ∀ a : H1 (M * r) ⊤ 𝒪, a ∈ cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp'.e i') →
      res a ∈ cornerSubmodule (M := H1 (M * r) H 𝒪) (Sp.e i) := by
    intro a ha
    refine hcofull (res a) fun g hg k => ?_
    obtain ⟨n, hn⟩ := IharaLemma.exists_pow_smul_corner_mem_maximalIdeal_smul (𝒪 := 𝒪) Sp' i'
      (tfull' g - algebraMap 𝒪 𝕋' (cfull g)) (hcfull' g hg) (V := H1 (M * r) ⊤ 𝒪) k
    exact ⟨n, by rw [← hcomm_pow g hg n a]; exact hpush k _ (hn a ha)⟩
  have hbwd : ∀ v : H1 (M * r) H 𝒪, v ∈ cornerSubmodule (M := H1 (M * r) H 𝒪) (Sp.e i) →
      ∃ a : H1 (M * r) ⊤ 𝒪, a ∈ cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp'.e i') ∧ v = res a := by
    intro v hv
    have hvr : v ∈ Set.range (iDeg' (M * r) (M * r) ⊤ H 1 𝒪 h₁) := by
      rw [hrange]; exact fun σ => hdiam σ v hv
    obtain ⟨a, rfl⟩ := hvr
    refine ⟨a, ?_, rfl⟩
    refine hcofull' a fun g hg k => ?_
    obtain ⟨n, hn⟩ := IharaLemma.exists_pow_smul_corner_mem_maximalIdeal_smul (𝒪 := 𝒪) Sp i
      (tfull g - algebraMap 𝒪 𝕋 (cfull g)) (hcfull g hg) (V := H1 (M * r) H 𝒪) k
    refine ⟨n, hpull k _ ?_⟩
    rw [hcomm_pow g hg n a]
    exact hn _ hv
  have hcorner_eq : (cornerSubmodule (M := H1 (M * r) H 𝒪) (Sp.e i)).restrictScalars 𝒪 =
      ((cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp'.e i')).restrictScalars 𝒪).map res := by
    ext v
    simp only [Submodule.restrictScalars_mem, Submodule.mem_map]
    constructor
    · intro hv
      obtain ⟨a, ha, rfl⟩ := hbwd v hv
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact hfwd a ha
  refine ⟨fun v => ⟨fun hv => hbwd v hv, fun ⟨a, ha, hva⟩ => hva ▸ hfwd a ha⟩,
    fun a _ h0 => hres_inj (by rw [h0, map_zero]), ?_, ?_⟩
  ·
    have e := Submodule.equivMapOfInjective res hres_inj
      ((cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp'.e i')).restrictScalars 𝒪)
    rw [← hcorner_eq] at e
    change Module.finrank 𝒪 ↥((cornerSubmodule (M := H1 (M * r) H 𝒪) (Sp.e i)).restrictScalars 𝒪) =
      Module.finrank 𝒪 ↥((cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp'.e i')).restrictScalars 𝒪)
    exact (LinearEquiv.finrank_eq e).symm
  ·

    set G : Set (CohCarrier.Gen (M * r) (↑S : Set ℕ)) :=
      {g | ∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ M * r), g = CohCarrier.Gen.U q hq hqL → q ∣ M} with hG

    have hmatch : ∀ f' ∈ Algebra.adjoin 𝒪 (CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 '' G),
        (∀ a : H1 (M * r) ⊤ 𝒪, a ∈ cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp'.e i') →
          f' a ∈ cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp'.e i')) ∧
        (∃ y' : 𝕋', ∀ a : H1 (M * r) ⊤ 𝒪, y' • a = f' a) ∧
        ∃ f ∈ Algebra.adjoin 𝒪 (CohCarrier.opFamily (M * r) H (↑S : Set ℕ) 𝒪 '' G),
          (∃ y : 𝕋, ∀ m : H1 (M * r) H 𝒪, y • m = f m) ∧ ∀ a : H1 (M * r) ⊤ 𝒪, res (f' a) = f (res a) := by
      intro f' hf'
      induction hf' using Algebra.adjoin_induction with
      | mem f' hf' =>
        obtain ⟨g, hg, rfl⟩ := hf'
        refine ⟨fun a ha => ?_, ⟨tfull' g, fun a => htfull' g hg a⟩, CohCarrier.opFamily (M * r) H (↑S : Set ℕ) 𝒪 g,
          Algebra.subset_adjoin ⟨g, hg, rfl⟩, ⟨tfull g, fun m => htfull g hg m⟩, fun a => ?_⟩
        · rw [← htfull' g hg a]; exact Submodule.smul_mem _ _ ha
        · rw [← htfull' g hg a, ← htfull g hg (res a)]; exact hcomm g hg a
      | algebraMap c =>
        refine ⟨fun a ha => ?_, ⟨algebraMap 𝒪 𝕋' c, fun a => ?_⟩, algebraMap 𝒪 _ c, Subalgebra.algebraMap_mem _ c,
          ⟨algebraMap 𝒪 𝕋 c, fun m => ?_⟩, fun a => ?_⟩
        · rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
          exact Submodule.smul_of_tower_mem _ c ha
        · rw [algebraMap_smul, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
        · rw [algebraMap_smul, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
        · rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
            LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply, map_smul]
      | add f₁ f₂ _ _ ih₁ ih₂ =>
        obtain ⟨hp₁, ⟨y₁', hy₁'⟩, f₁H, hf₁H, ⟨y₁, hy₁⟩, hr₁⟩ := ih₁
        obtain ⟨hp₂, ⟨y₂', hy₂'⟩, f₂H, hf₂H, ⟨y₂, hy₂⟩, hr₂⟩ := ih₂
        refine ⟨fun a ha => ?_, ⟨y₁' + y₂', fun a => ?_⟩, f₁H + f₂H, Subalgebra.add_mem _ hf₁H hf₂H,
          ⟨y₁ + y₂, fun m => ?_⟩, fun a => ?_⟩
        · rw [LinearMap.add_apply]; exact Submodule.add_mem _ (hp₁ a ha) (hp₂ a ha)
        · rw [add_smul, hy₁', hy₂', LinearMap.add_apply]
        · rw [add_smul, hy₁, hy₂, LinearMap.add_apply]
        · rw [LinearMap.add_apply, LinearMap.add_apply, map_add, hr₁, hr₂]
      | mul f₁ f₂ _ _ ih₁ ih₂ =>
        obtain ⟨hp₁, ⟨y₁', hy₁'⟩, f₁H, hf₁H, ⟨y₁, hy₁⟩, hr₁⟩ := ih₁
        obtain ⟨hp₂, ⟨y₂', hy₂'⟩, f₂H, hf₂H, ⟨y₂, hy₂⟩, hr₂⟩ := ih₂
        refine ⟨fun a ha => ?_, ⟨y₁' * y₂', fun a => ?_⟩, f₁H * f₂H, Subalgebra.mul_mem _ hf₁H hf₂H,
          ⟨y₁ * y₂, fun m => ?_⟩, fun a => ?_⟩
        · rw [Module.End.mul_apply]; exact hp₁ _ (hp₂ a ha)
        · rw [mul_smul, hy₂', hy₁', Module.End.mul_apply]
        · rw [mul_smul, hy₂, hy₁, Module.End.mul_apply]
        · rw [Module.End.mul_apply, Module.End.mul_apply, hr₁, hr₂]

    have hmatch' : ∀ f ∈ Algebra.adjoin 𝒪 (CohCarrier.opFamily (M * r) H (↑S : Set ℕ) 𝒪 '' G),
        ∃ f' ∈ Algebra.adjoin 𝒪 (CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 '' G),
          ∀ a : H1 (M * r) ⊤ 𝒪, res (f' a) = f (res a) := by
      intro f hf
      induction hf using Algebra.adjoin_induction with
      | mem f hf =>
        obtain ⟨g, hg, rfl⟩ := hf
        refine ⟨CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 g, Algebra.subset_adjoin ⟨g, hg, rfl⟩, fun a => ?_⟩
        rw [← htfull' g hg a, ← htfull g hg (res a)]; exact hcomm g hg a
      | algebraMap c =>
        refine ⟨algebraMap 𝒪 _ c, Subalgebra.algebraMap_mem _ c, fun a => ?_⟩
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
          LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply, map_smul]
      | add f₁ f₂ _ _ ih₁ ih₂ =>
        obtain ⟨f₁', hf₁', hr₁⟩ := ih₁
        obtain ⟨f₂', hf₂', hr₂⟩ := ih₂
        exact ⟨f₁' + f₂', Subalgebra.add_mem _ hf₁' hf₂', fun a => by
          rw [LinearMap.add_apply, LinearMap.add_apply, map_add, hr₁, hr₂]⟩
      | mul f₁ f₂ _ _ ih₁ ih₂ =>
        obtain ⟨f₁', hf₁', hr₁⟩ := ih₁
        obtain ⟨f₂', hf₂', hr₂⟩ := ih₂
        exact ⟨f₁' * f₂', Subalgebra.mul_mem _ hf₁' hf₂', fun a => by
          rw [Module.End.mul_apply, Module.End.mul_apply, hr₁, hr₂]⟩

    set C := Sp.CornerRing i
    set C' := Sp'.CornerRing i'
    let Rel : C → C' → Prop := fun x x' =>
      ∀ (a : H1 (M * r) ⊤ 𝒪) (ha : a ∈ cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp'.e i')),
        res (((x' • ⟨a, ha⟩ : ↥(cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp'.e i'))) : H1 (M * r) ⊤ 𝒪)) =
          (x : 𝕋) • res a

    have huniq : ∀ (x : C) (x₁ x₂ : C'), Rel x x₁ → Rel x x₂ → x₁ = x₂ := by
      intro x x₁ x₂ h1 h2
      rw [← sub_eq_zero]
      refine hfaith' _ fun m => ?_
      have hsub : ((x₁ - x₂) • m : ↥(cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp'.e i'))) = x₁ • m - x₂ • m :=
        sub_smul x₁ x₂ m
      rw [hsub, sub_eq_zero]
      apply Subtype.ext
      apply hres_inj
      rw [h1 m.1 m.2, h2 m.1 m.2]

    have hexists : ∀ x : C, ∃ x' : C', Rel x x' := by
      intro x
      obtain ⟨f, hf, hxf⟩ := hgen (x : 𝕋)
      obtain ⟨f', hf', hr⟩ := hmatch' f hf
      obtain ⟨hpres, ⟨y', hy'⟩, -⟩ := hmatch f' hf'
      refine ⟨Sp'.toCornerRing i' y', fun a ha => ?_⟩
      rw [IharaLemma.IdempotentSplitting.coe_cornerSmul, IharaLemma.IdempotentSplitting.coe_toCornerRing,
        mul_smul, mul_smul, hxf]
      show res (Sp'.e i' • y' • Sp'.e i' • a) = f (res a)
      rw [IharaLemma.IdempotentSplitting.e_smul_coe Sp' i' ⟨a, ha⟩, hy',
        IharaLemma.IdempotentSplitting.e_smul_coe Sp' i' ⟨f' a, hpres a ha⟩, hr]
    choose eDf heDf using hexists

    have hRel_one : Rel 1 1 := by
      intro a ha
      rw [one_smul, IharaLemma.IdempotentSplitting.coe_one_cornerRing]
      exact (IharaLemma.IdempotentSplitting.e_smul_coe Sp i ⟨res a, hfwd a ha⟩).symm
    have hRel_mul : ∀ x y : C, Rel (x * y) (eDf x * eDf y) := by
      intro x y a ha
      rw [show ((eDf x * eDf y) • (⟨a, ha⟩ : ↥(cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp'.e i')))) =
        eDf x • (eDf y • ⟨a, ha⟩) from
          mul_smul (eDf x) (eDf y) (⟨a, ha⟩ : ↥(cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp'.e i')))]
      set m := (eDf y • ⟨a, ha⟩ : ↥(cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp'.e i')))
      rw [heDf x m.1 m.2]
      show (x : 𝕋) • res ((eDf y • ⟨a, ha⟩ : ↥(cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp'.e i'))) : H1 (M * r) ⊤ 𝒪) = _
      rw [heDf y a ha, ← mul_smul]
      rfl
    have hRel_add : ∀ x y : C, Rel (x + y) (eDf x + eDf y) := by
      intro x y a ha
      rw [add_smul, Submodule.coe_add, map_add, heDf x a ha, heDf y a ha, ← add_smul]
      rfl
    have hRel_alg : ∀ c : 𝒪, Rel (algebraMap 𝒪 C c) (algebraMap 𝒪 C' c) := by
      intro c a ha
      rw [algebraMap_smul]
      show res (c • a) = ((algebraMap 𝒪 C c : C) : 𝕋) • res a
      rw [map_smul, IharaLemma.IdempotentSplitting.algebraMap_base_cornerRing_coe,
        mul_smul, mul_smul, IharaLemma.IdempotentSplitting.e_smul_coe Sp i ⟨res a, hfwd a ha⟩, algebraMap_smul]
      exact (IharaLemma.IdempotentSplitting.e_smul_coe Sp i ⟨c • res a, Submodule.smul_of_tower_mem _ c (hfwd a ha)⟩).symm

    let eDh : C →ₐ[𝒪] C' :=
      { toFun := eDf
        map_one' := huniq 1 _ _ (heDf 1) hRel_one
        map_mul' := fun x y => huniq _ _ _ (heDf _) (hRel_mul x y)
        map_zero' := by
          have h := huniq _ _ _ (heDf _) (hRel_add 0 0)
          rw [add_zero] at h
          exact left_eq_add.mp h |>.symm ▸ rfl
        map_add' := fun x y => huniq _ _ _ (heDf _) (hRel_add x y)
        commutes' := fun c => huniq _ _ _ (heDf _) (hRel_alg c) }
    have heDh : ∀ x, eDh x = eDf x := fun _ => rfl

    have hinjD : Function.Injective eDh := by
      intro x y hxy
      rw [← sub_eq_zero]
      refine hfaith _ fun m => ?_
      obtain ⟨a, ha, hma⟩ := hbwd m.1 m.2
      apply Subtype.ext
      rw [Submodule.coe_zero, IharaLemma.IdempotentSplitting.coe_cornerSmul, hma]
      have h1 := heDf x a ha
      have h2 := heDf y a ha
      rw [heDh, heDh] at hxy
      rw [hxy] at h1
      show ((x - y : C) : 𝕋) • res a = 0
      rw [show ((x - y : C) : 𝕋) = (x : 𝕋) - (y : 𝕋) from rfl, sub_smul, ← h1, ← h2, sub_self]
    have hsurjD : Function.Surjective eDh := by
      intro x'

      obtain ⟨f', hf', hxf'⟩ := hgen' (x' : 𝕋')
      obtain ⟨hpres, -, f, hf, ⟨y, hy⟩, hr⟩ := hmatch f' hf'
      refine ⟨Sp.toCornerRing i y, ?_⟩
      rw [heDh]
      refine huniq _ _ _ (heDf _) fun a ha => ?_
      rw [IharaLemma.IdempotentSplitting.coe_cornerSmul, hxf', IharaLemma.IdempotentSplitting.coe_toCornerRing, mul_smul,
        mul_smul, IharaLemma.IdempotentSplitting.e_smul_coe Sp i ⟨res a, hfwd a ha⟩, hy, ← hr]
      exact (IharaLemma.IdempotentSplitting.e_smul_coe Sp i ⟨res (f' a), hfwd _ (hpres a ha)⟩).symm
    refine ⟨AlgEquiv.ofBijective eDh ⟨hinjD, hsurjD⟩, fun g hg => ?_, fun x ac vc hva => ?_⟩
    · rw [AlgEquiv.ofBijective_apply, heDh]
      refine huniq _ _ _ (heDf _) fun a ha => ?_
      have hta : tfull' g • a ∈ cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp'.e i') := Submodule.smul_mem _ _ ha
      have hL : (((Sp'.toCornerRing i' (tfull' g)) • (⟨a, ha⟩ : ↥(cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp'.e i')))
          : ↥(cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp'.e i'))) : H1 (M * r) ⊤ 𝒪) = tfull' g • a := by
        rw [IharaLemma.IdempotentSplitting.coe_cornerSmul, IharaLemma.IdempotentSplitting.coe_toCornerRing, mul_smul, mul_smul]
        show Sp'.e i' • tfull' g • Sp'.e i' • a = tfull' g • a
        rw [IharaLemma.IdempotentSplitting.e_smul_coe Sp' i' ⟨a, ha⟩,
          IharaLemma.IdempotentSplitting.e_smul_coe Sp' i' ⟨tfull' g • a, hta⟩]
      have hR : ((Sp.toCornerRing i (tfull g) : C) : 𝕋) • res a = tfull g • res a := by
        rw [IharaLemma.IdempotentSplitting.coe_toCornerRing, mul_smul, mul_smul,
          IharaLemma.IdempotentSplitting.e_smul_coe Sp i ⟨res a, hfwd a ha⟩]
        exact IharaLemma.IdempotentSplitting.e_smul_coe Sp i ⟨tfull g • res a, Submodule.smul_mem _ _ (hfwd a ha)⟩
      rw [hL, hR]
      exact hcomm g hg a
    · rw [AlgEquiv.ofBijective_apply, heDh, heDf x ac.1 ac.2, IharaLemma.IdempotentSplitting.coe_cornerSmul, hva]

end S_CohCarrier_cornerSubmodule_sigmaCorner_gammaH_eq_map_iDegL_one_of_isUnit_index
end P2MW
export P2MW.S_CohCarrier_cornerSubmodule_sigmaCorner_gammaH_eq_map_iDegL_one_of_isUnit_index (solution)
