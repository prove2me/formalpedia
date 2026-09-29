-- Prove2me | solution 1 for CohCarrier.cornerSubmodule_sigmaCorner_gammaZero_auxLevel_eq_iDegL_sup_iDegL
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/1be8f88e-087b-5a7d-a034-457e4750ab5e

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CohCarrier_LevelPairing
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CohCarrier_Lower
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_LocalConditions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_coprime
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_dvd
import Theorems.Thm_IharaLemma_exists_pow_smul_corner_mem_maximalIdeal_smul
import Theorems.Thm_CohCarrier_isEis_kernel_pair_of_prime
import Theorems.Thm_CohCarrier_opFamily_comm
import Theorems.Thm_ResidualGaloisRep_exists_prime_modEq_one_isFrobeniusAt_eval_charpoly_ne_zero_of_isAbsolutelyIrreducible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_cornerSubmodule_sigmaCorner_gammaZero_auxLevel_eq_iDegL_sup_iDegL
p2m_attr_erase "instance" "Ihara.instGroupIharaAmalgam Ihara.instNormalSpecialLinearGroupFinOfNatNatZAwayPrincipalCongruenceAway FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.zAwayToZMod_algebraMap Ihara.gamma0AwayUnitsChar_coe Ihara.gamma0UnitsHom_coe Ihara.gamma0UnitsChar_apply Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.mennickeA_coe Ihara.mennickeU_coe Ihara.gamma0FinUnitsChar_coe Ihara.gamma0FinMap_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open Polynomial IsLocalRing CohCarrier IharaLemma IharaTower

namespace E5SigTr

section powlemmas
variable {𝒪 : Type} [CommRing 𝒪] {T V : Type} [CommRing T] [Algebra 𝒪 T]
  [AddCommGroup V] [Module 𝒪 V] [Module T V] [IsScalarTower 𝒪 T V]

theorem pow_sub_smul_eq (t : T) (f : Module.End 𝒪 V) (c : 𝒪) (ht : ∀ m : V, t • m = f m) :
    ∀ (n : ℕ) (m : V), (t - algebraMap 𝒪 T c) ^ n • m =
      ((f - algebraMap 𝒪 (Module.End 𝒪 V) c) ^ n) m := by
  intro n
  induction n with
  | zero => intro m; simp
  | succ n ih =>
    intro m
    rw [pow_succ', mul_smul, ih, pow_succ', Module.End.mul_apply, sub_smul, ht, LinearMap.sub_apply,
      Module.algebraMap_end_apply, algebraMap_smul]

end powlemmas

section commute
variable {𝒪 : Type} [CommRing 𝒪] {V W : Type} [AddCommGroup V] [Module 𝒪 V] [AddCommGroup W] [Module 𝒪 W]

theorem map_pow_sub_apply (ι : V →ₗ[𝒪] W) (f : Module.End 𝒪 V) (g : Module.End 𝒪 W) (c : 𝒪)
    (h : ∀ v, ι (f v) = g (ι v)) :
    ∀ (n : ℕ) (v : V), ι (((f - algebraMap 𝒪 (Module.End 𝒪 V) c) ^ n) v) =
      ((g - algebraMap 𝒪 (Module.End 𝒪 W) c) ^ n) (ι v) := by
  intro n
  induction n with
  | zero => intro v; simp
  | succ n ih =>
    intro v
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.sub_apply, map_sub, h, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]

theorem map_mem_pow_smul_top (ι : V →ₗ[𝒪] W) (I : Ideal 𝒪) (v : V) (hv : v ∈ (I • ⊤ : Submodule 𝒪 V)) :
    ι v ∈ (I • ⊤ : Submodule 𝒪 W) := by
  have : Submodule.map ι (I • ⊤ : Submodule 𝒪 V) ≤ I • ⊤ := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact this ⟨v, hv, rfl⟩

end commute

section diamond
open CongruenceSubgroup
open scoped MatrixGroups

theorem diamondL_top_apply (N : ℕ) [NeZero N] (𝒪 : Type) [CommRing 𝒪] (d : (ZMod N)ˣ)
    (φ : CohCarrier.H1 N ⊤ 𝒪) : CohCarrier.diamondL N ⊤ 𝒪 d φ = φ := by
  set σ := Classical.choose (CohCarrier.gamma0Units_surjective N d) with hσdef
  rw [CohCarrier.diamondL_eq_diamondRaw N ⊤ 𝒪 d σ (Classical.choose_spec (CohCarrier.gamma0Units_surjective N d))]
  have hσ : (σ : SL(2, ℤ)) ∈ CohCarrier.GammaH N ⊤ := by
    rw [CohCarrier.GammaH_top]; exact σ.2
  refine AddMonoidHom.ext fun x => ?_
  show φ (Additive.ofMul (CohCarrier.conjHom N ⊤ σ (Additive.toMul x))) = φ x
  have hconj : CohCarrier.conjHom N ⊤ σ (Additive.toMul x) =
      ⟨(σ : SL(2, ℤ)), hσ⟩ * Additive.toMul x * ⟨(σ : SL(2, ℤ)), hσ⟩⁻¹ := Subtype.ext rfl
  rw [hconj, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
  simp only [ofMul_toMul]
  abel

end diamond

section legs
variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
variable {M r : ℕ} [NeZero M] [NeZero r] [NeZero (M * r)] (hr : r.Prime) (hrM : ¬ r ∣ M) {S : Finset ℕ}

variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 (M * r) ⊤ 𝒪)] [IsScalarTower 𝒪 𝕋 (H1 (M * r) ⊤ 𝒪)]
variable (Sp : IdempotentSplitting 𝕋) (i : Fin Sp.n)
variable (tfull : CohCarrier.Gen (M * r) (↑S : Set ℕ) → 𝕋) (cfull : CohCarrier.Gen (M * r) (↑S : Set ℕ) → 𝒪)
variable (htfull : ∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ M * r), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      ∀ m : H1 (M * r) ⊤ 𝒪, tfull g • m = CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 g m)
variable (hcofull : ∀ v : H1 (M * r) ⊤ 𝒪, (∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ M * r), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      ∀ k : ℕ, ∃ n : ℕ, ((tfull g - algebraMap 𝒪 𝕋 (cfull g)) ^ n) • v ∈
        ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 (M * r) ⊤ 𝒪))) →
      v ∈ cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp.e i))
variable (hcd : ∀ d : (ZMod (M * r))ˣ, cfull (.dia d) - 1 ∈ IsLocalRing.maximalIdeal 𝒪)

variable {𝕋₀ : Type} [CommRing 𝕋₀] [Algebra 𝒪 𝕋₀] [Module 𝕋₀ (H1 M ⊤ 𝒪)] [IsScalarTower 𝒪 𝕋₀ (H1 M ⊤ 𝒪)]
  [Module.Finite 𝒪 𝕋₀]
variable (Sp₀ : IdempotentSplitting 𝕋₀) (i₀ : Fin Sp₀.n)
variable (tfull₀ : CohCarrier.Gen M (↑(insert r S) : Set ℕ) → 𝕋₀) (cfull₀ : CohCarrier.Gen M (↑(insert r S) : Set ℕ) → 𝒪)
variable (htfull₀ : ∀ g, ∀ m : H1 M ⊤ 𝒪, tfull₀ g • m = CohCarrier.opFamily M ⊤ (↑(insert r S) : Set ℕ) 𝒪 g m)
variable (hcfull₀ : ∀ g, tfull₀ g - algebraMap 𝒪 𝕋₀ (cfull₀ g) ∈ Sp₀.𝔪 i₀)
variable (hmatchT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ M * r)
        (hℓS' : ℓ ∉ (↑(insert r S) : Set ℕ)) (hℓM : ¬ ℓ ∣ M),
      cfull (.T ℓ hℓ hℓS hℓL) = cfull₀ (.T ℓ hℓ hℓS' hℓM))
variable (hmatchU : ∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ M * r) (hqM : q ∣ M), cfull (.U q hq hqL) = cfull₀ (.U q hq hqM))

variable {d : ℕ} [NeZero d] (hd : LevelLE M (M * r) ⊤ ⊤ d) (hdr : d = 1 ∨ d = r)

include hr hrM htfull hcofull hcd htfull₀ hcfull₀ hmatchT hmatchU hdr in
theorem iDegL_mem_corner (a : H1 M ⊤ 𝒪) (ha : a ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀)) :
    iDegL M (M * r) ⊤ ⊤ d 𝒪 𝒪 hd a ∈ cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp.e i) := by
  apply hcofull
  intro g hguard k

  have key : ∀ (g' : CohCarrier.Gen M (↑(insert r S) : Set ℕ)) (c : 𝒪), cfull₀ g' = c →
      (∀ v : H1 M ⊤ 𝒪, iDegL M (M * r) ⊤ ⊤ d 𝒪 𝒪 hd (CohCarrier.opFamily M ⊤ (↑(insert r S) : Set ℕ) 𝒪 g' v) =
        CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 g (iDegL M (M * r) ⊤ ⊤ d 𝒪 𝒪 hd v)) →
      cfull g = c →
      ∃ n : ℕ, (tfull g - algebraMap 𝒪 𝕋 (cfull g)) ^ n • iDegL M (M * r) ⊤ ⊤ d 𝒪 𝒪 hd a ∈
        ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 (M * r) ⊤ 𝒪)) := by
    intro g' c hc' hcomm hc
    obtain ⟨n, hn⟩ := IharaLemma.exists_pow_smul_corner_mem_maximalIdeal_smul (𝒪 := 𝒪) Sp₀ i₀
      (tfull₀ g' - algebraMap 𝒪 𝕋₀ (cfull₀ g')) (hcfull₀ g') (V := H1 M ⊤ 𝒪) k
    refine ⟨n, ?_⟩
    rw [pow_sub_smul_eq (tfull g) (CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 g) (cfull g) (htfull g hguard) n,
      hc, ← hc', ← map_pow_sub_apply (iDegL M (M * r) ⊤ ⊤ d 𝒪 𝒪 hd) _ _ (cfull₀ g') hcomm n a,
      ← pow_sub_smul_eq (tfull₀ g') _ (cfull₀ g') (htfull₀ g') n a]
    exact map_mem_pow_smul_top _ _ _ (hn a ha)
  cases g with
  | T ℓ hℓ hℓS hℓL =>
    have hℓM : ¬ ℓ ∣ M := fun h => hℓL (dvd_mul_of_dvd_left h r)
    have hℓr : ℓ ≠ r := fun h => hℓL (h ▸ dvd_mul_left r M)
    have hℓS' : ℓ ∉ (↑(insert r S) : Set ℕ) := by
      rw [Finset.coe_insert, Set.mem_insert_iff]
      rintro (h | h)
      · exact hℓr h
      · exact hℓS h
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hcop : Nat.Coprime ℓ d := by
      rcases hdr with rfl | rfl
      · exact Nat.coprime_one_right ℓ
      · exact (Nat.coprime_primes hℓ hr).mpr hℓr
    exact key (.T ℓ hℓ hℓS' hℓM) _ rfl
      (fun v => CohCarrier.iDeg_heckeT_comm_of_coprime hd hcop hℓ hℓL v) (hmatchT ℓ hℓ hℓS hℓL hℓS' hℓM)
  | U q hq hqL =>
    have hqM : q ∣ M := hguard q hq hqL rfl
    haveI : NeZero q := ⟨hq.ne_zero⟩
    have hqr : q ≠ r := fun h => hrM (h ▸ hqM)
    have hcop : Nat.Coprime q d := by
      rcases hdr with rfl | rfl
      · exact Nat.coprime_one_right q
      · exact (Nat.coprime_primes hq hr).mpr hqr
    exact key (.U q hq hqM) _ rfl
      (fun v => CohCarrier.iDeg_heckeT_comm_of_dvd hd hcop hqM v) (hmatchU q hq hqL hqM)
  | dia δ =>

    refine ⟨k, ?_⟩
    rw [pow_sub_smul_eq (tfull (.dia δ)) (CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 (.dia δ)) (cfull (.dia δ))
      (htfull _ hguard) k]
    have hop : CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 (.dia δ) -
        algebraMap 𝒪 (Module.End 𝒪 (H1 (M * r) ⊤ 𝒪)) (cfull (.dia δ)) =
        algebraMap 𝒪 (Module.End 𝒪 (H1 (M * r) ⊤ 𝒪)) (1 - cfull (.dia δ)) := by
      rw [map_sub, map_one]
      congr 1
      exact LinearMap.ext fun φ => diamondL_top_apply (M * r) 𝒪 δ φ
    rw [hop, ← map_pow, Module.algebraMap_end_apply]
    apply Submodule.smul_mem_smul
    · have : 1 - cfull (.dia δ) ∈ IsLocalRing.maximalIdeal 𝒪 := by
        rw [← neg_sub]; exact (IsLocalRing.maximalIdeal 𝒪).neg_mem (hcd δ)
      exact Ideal.pow_mem_pow this k
    · exact Submodule.mem_top

end legs

end E5SigTr

namespace E5SigTr

section noneis
variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]

theorem isUnit_toCornerRing_add_algebraMap {B : Type} [CommRing B] [Algebra 𝒪 B]
    (Sp : IdempotentSplitting B) (i : Fin Sp.n) (x : B) (hx : x ∈ Sp.𝔪 i) (c : 𝒪) (hc : IsUnit c) :
    IsUnit (Sp.toCornerRing i (x + algebraMap 𝒪 B c)) := by
  have hxm : Sp.toCornerRing i x ∈ maximalIdeal (Sp.CornerRing i) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Sp.CornerRing i) (Sp.𝔪 i) x).mpr hx
  have hcu : IsUnit (Sp.toCornerRing i (algebraMap 𝒪 B c)) := by
    have : Sp.toCornerRing i (algebraMap 𝒪 B c) = algebraMap 𝒪 (Sp.CornerRing i) c := rfl
    rw [this]
    exact hc.map _
  rw [map_add]

  obtain ⟨u, hu⟩ := hcu
  rw [← hu]
  have hm : (↑u⁻¹ : Sp.CornerRing i) * Sp.toCornerRing i x ∈ maximalIdeal (Sp.CornerRing i) :=
    Ideal.mul_mem_left _ _ hxm
  have h1 : IsUnit (1 + (↑u⁻¹ : Sp.CornerRing i) * Sp.toCornerRing i x) := by
    have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-((↑u⁻¹ : Sp.CornerRing i) * Sp.toCornerRing i x))
      (by rw [← IsLocalRing.mem_maximalIdeal]; exact (maximalIdeal (Sp.CornerRing i)).neg_mem hm)
    rwa [sub_neg_eq_add] at this
  have : Sp.toCornerRing i x + ↑u = ↑u * (1 + ↑u⁻¹ * Sp.toCornerRing i x) := by
    rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul, add_comm]
  rw [this]
  exact (Units.isUnit u).mul h1

variable {M : ℕ} [NeZero M] {S' : Set ℕ}
variable {𝕋₀ : Type} [CommRing 𝕋₀] [Algebra 𝒪 𝕋₀] [Module 𝕋₀ (H1 M ⊤ 𝒪)] [IsScalarTower 𝒪 𝕋₀ (H1 M ⊤ 𝒪)]
variable (Sp₀ : IdempotentSplitting 𝕋₀) (i₀ : Fin Sp₀.n)
variable (tfull₀ : CohCarrier.Gen M S' → 𝕋₀) (cfull₀ : CohCarrier.Gen M S' → 𝒪)
variable (htfull₀ : ∀ g, ∀ m : H1 M ⊤ 𝒪, tfull₀ g • m = CohCarrier.opFamily M ⊤ S' 𝒪 g m)
variable (hcfull₀ : ∀ g, tfull₀ g - algebraMap 𝒪 𝕋₀ (cfull₀ g) ∈ Sp₀.𝔪 i₀)

include htfull₀ hcfull₀ in

theorem eq_zero_of_isEis_of_mem_corner (ℓ₀ : ℕ) (hℓ : ℓ₀.Prime) (hℓS : ℓ₀ ∉ S') (hℓM : ¬ ℓ₀ ∣ M)
    (hne : IsUnit (cfull₀ (.T ℓ₀ hℓ hℓS hℓM) - ((ℓ₀ : 𝒪) + 1)))
    (g : H1 M ⊤ 𝒪) (hg : g ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀))
    (hEis : haveI : NeZero ℓ₀ := ⟨hℓ.ne_zero⟩; IsEis 𝒪 𝒪 M ⊤ ℓ₀ g) : g = 0 := by
  haveI : NeZero ℓ₀ := ⟨hℓ.ne_zero⟩
  set u : 𝕋₀ := tfull₀ (.T ℓ₀ hℓ hℓS hℓM) - algebraMap 𝒪 𝕋₀ ((ℓ₀ : 𝒪) + 1) with hu

  have hug : u • g = 0 := by
    rw [hu, sub_smul, htfull₀, algebraMap_smul]
    show heckeT M ⊤ ℓ₀ 𝒪 g - ((ℓ₀ : 𝒪) + 1) • g = 0
    rw [hEis, sub_self]

  have hunit : IsUnit (Sp₀.toCornerRing i₀ u) := by
    have : u = (tfull₀ (.T ℓ₀ hℓ hℓS hℓM) - algebraMap 𝒪 𝕋₀ (cfull₀ (.T ℓ₀ hℓ hℓS hℓM))) +
        algebraMap 𝒪 𝕋₀ (cfull₀ (.T ℓ₀ hℓ hℓS hℓM) - ((ℓ₀ : 𝒪) + 1)) := by
      rw [hu, map_sub]; ring
    rw [this]
    exact isUnit_toCornerRing_add_algebraMap Sp₀ i₀ _ (hcfull₀ _) _ hne

  obtain ⟨y, hy⟩ := hunit.exists_left_inv
  have hval : (y : 𝕋₀) * (Sp₀.e i₀ * u * Sp₀.e i₀) = Sp₀.e i₀ := congrArg Subtype.val hy
  have heg : Sp₀.e i₀ • g = g := Sp₀.e_smul_coe i₀ ⟨g, hg⟩
  calc g = Sp₀.e i₀ • g := heg.symm
    _ = ((y : 𝕋₀) * (Sp₀.e i₀ * u * Sp₀.e i₀)) • g := by rw [hval]
    _ = 0 := by rw [mul_smul, mul_smul, mul_smul, heg, hug, smul_zero, smul_zero]

end noneis

section prime
variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]

theorem exists_nonEis_prime (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (M r : ℕ) [NeZero M] (hr : r.Prime)
    [Fact (CuspForm.HasIntegralStructure M 2)]
    (θ : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓM hℓS)) * X + C (ℓ : ResidueField 𝒪)) :
    ∃ (ℓ₀ : ℕ) (hℓ : ℓ₀.Prime) (hℓM : ¬ ℓ₀ ∣ M) (hℓS : ℓ₀ ∉ (↑S : Set ℕ)),
      ℓ₀ ≠ r ∧ θ (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) ≠ (ℓ₀ : ResidueField 𝒪) + 1 := by
  have hpos : 0 < M * r * ∏ q ∈ S, q := by
    apply Nat.pos_of_ne_zero
    apply mul_ne_zero (mul_ne_zero (NeZero.ne M) hr.ne_zero)
    exact Finset.prod_ne_zero_iff.mpr fun q hq => (hS q hq).ne_zero
  obtain ⟨ℓ, A, σ, hℓ, hℓdvd, -, hA, hσ, hev⟩ :=
    ρbar.exists_prime_modEq_one_isFrobeniusAt_eval_charpoly_ne_zero_of_isAbsolutelyIrreducible habs 1 hpos
  have hℓM : ¬ ℓ ∣ M := fun h => hℓdvd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h r) _)
  have hℓr : ℓ ≠ r := fun h => hℓdvd (dvd_mul_of_dvd_left (h ▸ dvd_mul_left r M) _)
  have hℓS : ℓ ∉ (↑S : Set ℕ) := fun h =>
    hℓdvd (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_coe.mp h)) _)
  refine ⟨ℓ, hℓ, hℓM, hℓS, hℓr, fun heq => hev ?_⟩
  rw [hθ ℓ hℓ hℓM hℓS A hA σ hσ, heq]
  simp

end prime

end E5SigTr

namespace E5SigTr

section inj
variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
variable {M r : ℕ} [NeZero M] [NeZero r] [NeZero (M * r)] (hr : r.Prime) (hrM : ¬ r ∣ M)
variable (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
variable (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime)
variable [Fact (CuspForm.HasIntegralStructure M 2)]
variable (θ : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
variable (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓM hℓS)) * X + C (ℓ : ResidueField 𝒪))
variable (cfull : CohCarrier.Gen (M * r) (↑S : Set ℕ) → 𝒪)
variable (hcT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ M * r),
      IsLocalRing.residue 𝒪 (cfull (.T ℓ hℓ hℓS hℓL)) = θ (CuspForm.heckeAlgebra.T hℓ hℓM hℓS))
variable {𝕋₀ : Type} [CommRing 𝕋₀] [Algebra 𝒪 𝕋₀] [Module 𝕋₀ (H1 M ⊤ 𝒪)] [IsScalarTower 𝒪 𝕋₀ (H1 M ⊤ 𝒪)]
variable (Sp₀ : IdempotentSplitting 𝕋₀) (i₀ : Fin Sp₀.n)
variable (tfull₀ : CohCarrier.Gen M (↑(insert r S) : Set ℕ) → 𝕋₀) (cfull₀ : CohCarrier.Gen M (↑(insert r S) : Set ℕ) → 𝒪)
variable (htfull₀ : ∀ g, ∀ m : H1 M ⊤ 𝒪, tfull₀ g • m = CohCarrier.opFamily M ⊤ (↑(insert r S) : Set ℕ) 𝒪 g m)
variable (hcfull₀ : ∀ g, tfull₀ g - algebraMap 𝒪 𝕋₀ (cfull₀ g) ∈ Sp₀.𝔪 i₀)
variable (hmatchT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ M * r)
        (hℓS' : ℓ ∉ (↑(insert r S) : Set ℕ)) (hℓM : ¬ ℓ ∣ M),
      cfull (.T ℓ hℓ hℓS hℓL) = cfull₀ (.T ℓ hℓ hℓS' hℓM))
variable (h1 : LevelLE M (M * r) ⊤ ⊤ 1) (hr' : LevelLE M (M * r) ⊤ ⊤ r)

theorem levelLE_up_one : LevelLE (M * r) (M * r * r) ⊤ ⊤ 1 :=
  ⟨dvd_mul_right _ _, one_dvd _, fun _ _ => Subgroup.mem_top _⟩

include hr in
theorem levelLE_up_r : LevelLE (M * r) (M * r * r) ⊤ ⊤ r :=
  ⟨dvd_mul_right _ _, by
    rw [Nat.mul_div_cancel_left r (Nat.pos_of_ne_zero (mul_ne_zero (NeZero.ne M) hr.ne_zero))],
    fun _ _ => Subgroup.mem_top _⟩

include hr habs hS hθ hcT htfull₀ hcfull₀ hmatchT in

theorem exists_prime_corner_eq_zero_of_isEis :
    ∃ (ℓ₀ : ℕ) (_ : NeZero ℓ₀), ℓ₀.Prime ∧ ¬ ℓ₀ ∣ M * r ∧
      ∀ g : H1 M ⊤ 𝒪, g ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) → IsEis 𝒪 𝒪 M ⊤ ℓ₀ g → g = 0 := by
  obtain ⟨ℓ₀, hℓ, hℓM, hℓS, hℓr, hne⟩ := exists_nonEis_prime ρbar habs S hS M r hr θ hθ
  haveI : NeZero ℓ₀ := ⟨hℓ.ne_zero⟩
  have hℓL : ¬ ℓ₀ ∣ M * r := fun h => ((Nat.Prime.dvd_mul hℓ).mp h).elim hℓM
    (fun h' => hℓr ((Nat.prime_dvd_prime_iff_eq hℓ hr).mp h'))
  have hℓS' : ℓ₀ ∉ (↑(insert r S) : Set ℕ) := by
    rw [Finset.coe_insert, Set.mem_insert_iff]; rintro (h | h); exacts [hℓr h, hℓS h]
  refine ⟨ℓ₀, inferInstance, hℓ, hℓL, fun g hg hEis => ?_⟩
  apply eq_zero_of_isEis_of_mem_corner Sp₀ i₀ tfull₀ cfull₀ htfull₀ hcfull₀ ℓ₀ hℓ hℓS' hℓM ?_ g hg hEis

  have hres : residue 𝒪 (cfull₀ (.T ℓ₀ hℓ hℓS' hℓM) - ((ℓ₀ : 𝒪) + 1)) ≠ 0 := by
    rw [map_sub, ← hmatchT ℓ₀ hℓ hℓS hℓL hℓS' hℓM, hcT ℓ₀ hℓ hℓM hℓS hℓL, map_add, map_natCast, map_one]
    exact sub_ne_zero.mpr hne
  by_contra hnu
  apply hres
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
  exact mem_nonunits_iff.mpr hnu

include hr hrM habs hS hθ hcT htfull₀ hcfull₀ hmatchT in

theorem legs_injective (a b : H1 M ⊤ 𝒪) (ha : a ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀))
    (hb : b ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀))
    (hab : iDegL M (M * r) ⊤ ⊤ 1 𝒪 𝒪 h1 a + iDegL M (M * r) ⊤ ⊤ r 𝒪 𝒪 hr' b = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨ℓ₀, _, hℓ, hℓL, hzero⟩ := exists_prime_corner_eq_zero_of_isEis hr ρbar habs S hS θ hθ cfull hcT
    Sp₀ i₀ tfull₀ cfull₀ htfull₀ hcfull₀ hmatchT
  have hI := (CohCarrier.isEis_kernel_pair_of_prime 𝒪 𝒪 ℓ₀ M r h1 hr' levelLE_up_one (levelLE_up_r hr)
    hr hrM hℓ hℓL).1 a b hab
  exact ⟨hzero a ha hI.1, hzero b hb hI.2⟩

end inj

end E5SigTr

namespace E5SigTr

section transferNat
open MonoidHom Subgroup

theorem map_diff {G : Type} [Group G] {K : Subgroup G} {A B : Type} [CommGroup A] [CommGroup B]
    (ϕ : ↥K →* A) (f : A →* B) (S T : K.LeftTransversal) [K.FiniteIndex] :
    f (Subgroup.leftTransversals.diff ϕ S T) = Subgroup.leftTransversals.diff (f.comp ϕ) S T := by
  unfold Subgroup.leftTransversals.diff
  rw [map_prod]
  rfl

theorem map_transfer {G : Type} [Group G] {K : Subgroup G} {A B : Type} [CommGroup A] [CommGroup B]
    (ϕ : ↥K →* A) (f : A →* B) [K.FiniteIndex] (g : G) :
    f (MonoidHom.transfer ϕ g) = MonoidHom.transfer (f.comp ϕ) g := by
  rw [MonoidHom.transfer_def ϕ default, MonoidHom.transfer_def (f.comp ϕ) default, map_diff]

theorem heckeT_comp {A B : Type} [AddCommGroup A] [AddCommGroup B] (N : ℕ) (H : Subgroup (ZMod N)ˣ)
    (ℓ : ℕ) [NeZero ℓ] (f : A →+ B) (φ : H1 N H A) :
    heckeT N H ℓ B (f.comp φ) = f.comp (heckeT N H ℓ A φ) := by
  refine AddMonoidHom.ext fun x => ?_
  show Multiplicative.toAdd (MonoidHom.transfer
      ((AddMonoidHom.toMultiplicativeRight (f.comp φ)).comp (conjL N H ℓ)) (Additive.toMul x)) =
    f (Multiplicative.toAdd (MonoidHom.transfer
      ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL N H ℓ)) (Additive.toMul x)))
  have hf : (AddMonoidHom.toMultiplicativeRight (f.comp φ)).comp (conjL N H ℓ) =
      (AddMonoidHom.toMultiplicative f).comp ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL N H ℓ)) := by
    ext; rfl
  rw [hf, ← map_transfer]
  rfl

end transferNat

section reduction
variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
variable (N : ℕ) (H : Subgroup (ZMod N)ˣ)

noncomputable def redH : H1 N H 𝒪 →ₗ[𝒪] H1 N H (ResidueField 𝒪) where
  toFun φ := (residue 𝒪).toAddMonoidHom.comp φ
  map_add' φ ψ := by ext; simp
  map_smul' c φ := by
    ext x
    show residue 𝒪 (c * φ x) = c • residue 𝒪 (φ x)
    rw [map_mul, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq]

theorem redH_apply (φ : H1 N H 𝒪) (x : Additive ↥(GammaH N H)) : redH N H φ x = residue 𝒪 (φ x) := rfl

theorem redH_eq_comp (φ : H1 N H 𝒪) : redH N H φ = (residue 𝒪).toAddMonoidHom.comp φ := rfl

theorem exists_eq_smul_of_redH_eq_zero [IsDomain 𝒪] (ϖ : 𝒪) (hϖ : maximalIdeal 𝒪 = Ideal.span {ϖ})
    (hϖ0 : ϖ ≠ 0) (φ : H1 N H 𝒪) (h : redH N H φ = 0) : ∃ ψ : H1 N H 𝒪, φ = ϖ • ψ := by
  have hx : ∀ x, ∃ c : 𝒪, φ x = ϖ * c := by
    intro x
    have : φ x ∈ maximalIdeal 𝒪 := by
      rw [← residue_eq_zero_iff]; exact DFunLike.congr_fun h x
    rw [hϖ, Ideal.mem_span_singleton'] at this
    obtain ⟨c, hc⟩ := this
    exact ⟨c, by rw [← hc, mul_comm]⟩
  choose c hc using hx
  refine ⟨{ toFun := c, map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · apply mul_left_cancel₀ hϖ0
    rw [← hc, map_zero, mul_zero]
  · intro x y
    apply mul_left_cancel₀ hϖ0
    rw [← hc, map_add, hc, hc, mul_add]
  · ext x
    exact hc x

variable {M M' : ℕ} {H₀ : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ} {d : ℕ} [NeZero d]

theorem redH_iDegL (h : LevelLE M M' H₀ H' d) (φ : H1 M H₀ 𝒪) :
    redH M' H' (iDegL M M' H₀ H' d 𝒪 𝒪 h φ) = iDegL M M' H₀ H' d (ResidueField 𝒪) 𝒪 h (redH M H₀ φ) := rfl

theorem redH_heckeT (ℓ : ℕ) [NeZero ℓ] (φ : H1 N H 𝒪) :
    redH N H (heckeT N H ℓ 𝒪 φ) = heckeT N H ℓ (ResidueField 𝒪) (redH N H φ) := by
  rw [redH_eq_comp, redH_eq_comp, heckeT_comp]

theorem smul_eq_zero_H1 [IsDomain 𝒪] (ϖ : 𝒪) (hϖ0 : ϖ ≠ 0) (φ : H1 N H 𝒪) (h : ϖ • φ = 0) : φ = 0 := by
  ext x
  have := DFunLike.congr_fun h x
  exact (mul_eq_zero.mp this).resolve_left hϖ0

end reduction

end E5SigTr

namespace E5SigTr

section closing
variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
variable {V : Type} [AddCommGroup V] [Module 𝒪 V]

theorem le_of_finrank_le_of_saturated (C D : Submodule 𝒪 V) (hDC : D ≤ C) [Module.Finite 𝒪 ↥C]
    (hrank : Module.finrank 𝒪 ↥C ≤ Module.finrank 𝒪 ↥D)
    (ϖ : 𝒪) (hirr : Irreducible ϖ) (hsat : ∀ v ∈ C, ϖ • v ∈ D → v ∈ D) : C ≤ D := by

  let D' : Submodule 𝒪 ↥C := D.comap C.subtype
  have hD' : Module.finrank 𝒪 ↥D' = Module.finrank 𝒪 ↥D :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hDC)
  have hq : Module.finrank 𝒪 (↥C ⧸ D') = 0 := by
    have := Submodule.finrank_quotient_add_finrank D'
    omega

  have htors : ∀ x : ↥C ⧸ D', ∃ c : 𝒪, c ≠ 0 ∧ c • x = 0 := by
    have : Module.IsTorsion 𝒪 (↥C ⧸ D') := (Module.finrank_eq_zero_iff_isTorsion).mp hq
    intro x
    obtain ⟨c, hc⟩ := @this x
    exact ⟨c, nonZeroDivisors.ne_zero c.2, hc⟩

  have hsat' : ∀ (n : ℕ) (v : V), v ∈ C → ϖ ^ n • v ∈ D → v ∈ D := by
    intro n
    induction n with
    | zero => intro v _ hv; simpa using hv
    | succ n ih =>
      intro v hvC hv
      rw [pow_succ', mul_smul] at hv
      exact ih v hvC (hsat _ (C.smul_mem _ hvC) hv)
  intro v hvC
  obtain ⟨c, hc0, hc⟩ := htors (Submodule.Quotient.mk ⟨v, hvC⟩)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hirr
  have hmem : c • (⟨v, hvC⟩ : ↥C) ∈ D' := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]; exact hc
  have : ϖ ^ n • v ∈ D := by
    have h2 : (↑u⁻¹ * c) • v ∈ D := by rw [mul_smul]; exact D.smul_mem _ hmem
    rwa [hu, ← mul_assoc, Units.inv_mul, one_mul] at h2
  exact hsat' n v hvC this

end closing

section sat
variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsDomain 𝒪]
variable {M : ℕ} [NeZero M] {S' : Set ℕ}
variable {𝕋₀ : Type} [CommRing 𝕋₀] [Algebra 𝒪 𝕋₀] [Module 𝕋₀ (H1 M ⊤ 𝒪)] [IsScalarTower 𝒪 𝕋₀ (H1 M ⊤ 𝒪)]
variable (Sp₀ : IdempotentSplitting 𝕋₀) (i₀ : Fin Sp₀.n)

theorem exists_mem_corner_eq_smul (u : 𝕋₀) (hunit : IsUnit (Sp₀.toCornerRing i₀ u))
    (a : H1 M ⊤ 𝒪) (ha : a ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀)) (c : 𝒪) (w : H1 M ⊤ 𝒪)
    (h : u • a = c • w) : ∃ a', a' ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) ∧ a = c • a' := by
  obtain ⟨y, hy⟩ := hunit.exists_left_inv
  have hval : (y : 𝕋₀) * (Sp₀.e i₀ * u * Sp₀.e i₀) = Sp₀.e i₀ := congrArg Subtype.val hy
  have heg : Sp₀.e i₀ • a = a := Sp₀.e_smul_coe i₀ ⟨a, ha⟩
  refine ⟨(y : 𝕋₀) • (Sp₀.e i₀ • w), Submodule.smul_mem _ _ ⟨w, rfl⟩, ?_⟩
  calc a = Sp₀.e i₀ • a := heg.symm
    _ = ((y : 𝕋₀) * (Sp₀.e i₀ * u * Sp₀.e i₀)) • a := by rw [hval]
    _ = (y : 𝕋₀) • (Sp₀.e i₀ • (c • w)) := by rw [mul_smul, mul_smul, mul_smul, heg, h]
    _ = c • ((y : 𝕋₀) • (Sp₀.e i₀ • w)) := by
        rw [smul_algebra_smul_comm c (Sp₀.e i₀) w, smul_algebra_smul_comm c (y : 𝕋₀) (Sp₀.e i₀ • w)]

variable (tfull₀ : CohCarrier.Gen M S' → 𝕋₀) (cfull₀ : CohCarrier.Gen M S' → 𝒪)
variable (htfull₀ : ∀ g, ∀ m : H1 M ⊤ 𝒪, tfull₀ g • m = CohCarrier.opFamily M ⊤ S' 𝒪 g m)
variable (hcfull₀ : ∀ g, tfull₀ g - algebraMap 𝒪 𝕋₀ (cfull₀ g) ∈ Sp₀.𝔪 i₀)

include htfull₀ hcfull₀ in

theorem exists_eq_smul_of_isEis_redH (ϖ : 𝒪) (hϖ : maximalIdeal 𝒪 = Ideal.span {ϖ}) (hϖ0 : ϖ ≠ 0)
    (ℓ₀ : ℕ) (hℓ : ℓ₀.Prime) (hℓS : ℓ₀ ∉ S') (hℓM : ¬ ℓ₀ ∣ M)
    (hne : IsUnit (cfull₀ (.T ℓ₀ hℓ hℓS hℓM) - ((ℓ₀ : 𝒪) + 1)))
    (a : H1 M ⊤ 𝒪) (ha : a ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀))
    (hEis : haveI : NeZero ℓ₀ := ⟨hℓ.ne_zero⟩; IsEis 𝒪 (ResidueField 𝒪) M ⊤ ℓ₀ (redH M ⊤ a)) :
    ∃ a', a' ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) ∧ a = ϖ • a' := by
  haveI : NeZero ℓ₀ := ⟨hℓ.ne_zero⟩
  set u : 𝕋₀ := tfull₀ (.T ℓ₀ hℓ hℓS hℓM) - algebraMap 𝒪 𝕋₀ ((ℓ₀ : 𝒪) + 1) with hu

  have hred : redH M ⊤ (u • a) = 0 := by
    rw [hu, sub_smul, htfull₀, algebraMap_smul, map_sub, map_smul]
    show redH M ⊤ (heckeT M ⊤ ℓ₀ 𝒪 a) - ((ℓ₀ : 𝒪) + 1) • redH M ⊤ a = 0
    rw [redH_heckeT, hEis, sub_self]
  obtain ⟨w, hw⟩ := exists_eq_smul_of_redH_eq_zero M ⊤ ϖ hϖ hϖ0 _ hred
  have hunit : IsUnit (Sp₀.toCornerRing i₀ u) := by
    have : u = (tfull₀ (.T ℓ₀ hℓ hℓS hℓM) - algebraMap 𝒪 𝕋₀ (cfull₀ (.T ℓ₀ hℓ hℓS hℓM))) +
        algebraMap 𝒪 𝕋₀ (cfull₀ (.T ℓ₀ hℓ hℓS hℓM) - ((ℓ₀ : 𝒪) + 1)) := by
      rw [hu, map_sub]; ring
    rw [this]
    exact isUnit_toCornerRing_add_algebraMap Sp₀ i₀ _ (hcfull₀ _) _ hne
  exact exists_mem_corner_eq_smul Sp₀ i₀ u hunit a ha ϖ w hw

end sat

end E5SigTr

namespace E5SigTr

section prime2
variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
variable {M r : ℕ} [NeZero M] (hr : r.Prime)
variable (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
variable (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime)
variable [Fact (CuspForm.HasIntegralStructure M 2)]
variable (θ : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
variable (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓM hℓS)) * X + C (ℓ : ResidueField 𝒪))
variable (cfull : CohCarrier.Gen (M * r) (↑S : Set ℕ) → 𝒪)
variable (hcT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ M * r),
      IsLocalRing.residue 𝒪 (cfull (.T ℓ hℓ hℓS hℓL)) = θ (CuspForm.heckeAlgebra.T hℓ hℓM hℓS))
variable (cfull₀ : CohCarrier.Gen M (↑(insert r S) : Set ℕ) → 𝒪)
variable (hmatchT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ M * r)
        (hℓS' : ℓ ∉ (↑(insert r S) : Set ℕ)) (hℓM : ¬ ℓ ∣ M),
      cfull (.T ℓ hℓ hℓS hℓL) = cfull₀ (.T ℓ hℓ hℓS' hℓM))

include hr habs hS hθ hcT hmatchT in

theorem exists_nonEis_prime_unit :
    ∃ (ℓ₀ : ℕ) (hℓ : ℓ₀.Prime) (hℓS' : ℓ₀ ∉ (↑(insert r S) : Set ℕ)) (hℓM : ¬ ℓ₀ ∣ M),
      ¬ ℓ₀ ∣ M * r ∧ IsUnit (cfull₀ (.T ℓ₀ hℓ hℓS' hℓM) - ((ℓ₀ : 𝒪) + 1)) := by
  obtain ⟨ℓ₀, hℓ, hℓM, hℓS, hℓr, hne⟩ := exists_nonEis_prime ρbar habs S hS M r hr θ hθ
  have hℓL : ¬ ℓ₀ ∣ M * r := fun h => ((Nat.Prime.dvd_mul hℓ).mp h).elim hℓM
    (fun h' => hℓr ((Nat.prime_dvd_prime_iff_eq hℓ hr).mp h'))
  have hℓS' : ℓ₀ ∉ (↑(insert r S) : Set ℕ) := by
    rw [Finset.coe_insert, Set.mem_insert_iff]; rintro (h | h); exacts [hℓr h, hℓS h]
  refine ⟨ℓ₀, hℓ, hℓS', hℓM, hℓL, ?_⟩
  have hres : residue 𝒪 (cfull₀ (.T ℓ₀ hℓ hℓS' hℓM) - ((ℓ₀ : 𝒪) + 1)) ≠ 0 := by
    rw [map_sub, ← hmatchT ℓ₀ hℓ hℓS hℓL hℓS' hℓM, hcT ℓ₀ hℓ hℓM hℓS hℓL, map_add, map_natCast, map_one]
    exact sub_ne_zero.mpr hne
  by_contra hnu
  apply hres
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
  exact mem_nonunits_iff.mpr hnu

end prime2

section misc
variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]

theorem smul_H1_residueField_eq_zero (N : ℕ) (H : Subgroup (ZMod N)ˣ) (ϖ : 𝒪) (hϖ : ϖ ∈ maximalIdeal 𝒪)
    (ψ : H1 N H (ResidueField 𝒪)) : ϖ • ψ = 0 := by
  ext x
  show ϖ • ψ x = 0
  rw [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq, (residue_eq_zero_iff ϖ).mpr hϖ, zero_mul]

end misc

end E5SigTr

namespace E5SigTr

section adjoinCorner
variable {𝒪 : Type} [CommRing 𝒪]
variable {M : ℕ} [NeZero M] {S' : Set ℕ}
variable {𝕋₀ : Type} [CommRing 𝕋₀] [Algebra 𝒪 𝕋₀] [Module 𝕋₀ (H1 M ⊤ 𝒪)] [IsScalarTower 𝒪 𝕋₀ (H1 M ⊤ 𝒪)]
variable (Sp₀ : IdempotentSplitting 𝕋₀) (i₀ : Fin Sp₀.n)
variable (hgen₀ : ∀ x : 𝕋₀, ∃ f ∈ Algebra.adjoin 𝒪 (Set.range (CohCarrier.opFamily M ⊤ S' 𝒪)),
      ∀ m : H1 M ⊤ 𝒪, x • m = f m)

theorem commute_of_mem_adjoin_opFamily {f g : Module.End 𝒪 (H1 M ⊤ 𝒪)}
    (hf : f ∈ Algebra.adjoin 𝒪 (Set.range (CohCarrier.opFamily M ⊤ S' 𝒪)))
    (hg : g ∈ Algebra.adjoin 𝒪 (Set.range (CohCarrier.opFamily M ⊤ S' 𝒪))) : Commute f g := by
  apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute hg
  rintro _ ⟨b, rfl⟩
  apply Commute.symm
  apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute hf
  rintro _ ⟨a, rfl⟩
  exact CohCarrier.opFamily_comm S' 𝒪 M ⊤ b a

include hgen₀ in

theorem apply_mem_corner_of_mem_adjoin {f : Module.End 𝒪 (H1 M ⊤ 𝒪)}
    (hf : f ∈ Algebra.adjoin 𝒪 (Set.range (CohCarrier.opFamily M ⊤ S' 𝒪)))
    (a : H1 M ⊤ 𝒪) (ha : a ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀)) :
    f a ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) := by
  obtain ⟨fe, hfe, hfe'⟩ := hgen₀ (Sp₀.e i₀)
  have hea : Sp₀.e i₀ • a = a := Sp₀.e_smul_coe i₀ ⟨a, ha⟩
  have hc := commute_of_mem_adjoin_opFamily hf hfe
  refine ⟨f a, ?_⟩
  show Sp₀.e i₀ • f a = f a
  rw [hfe', ← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply, ← hfe', hea]

end adjoinCorner

section diag
variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
variable {M r : ℕ} [NeZero M] [NeZero r] [NeZero (M * r)] (hr : r.Prime) (hrM : ¬ r ∣ M) {S : Finset ℕ}
variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 (M * r) ⊤ 𝒪)] [IsScalarTower 𝒪 𝕋 (H1 (M * r) ⊤ 𝒪)]
variable (tfull : CohCarrier.Gen (M * r) (↑S : Set ℕ) → 𝕋)
variable (hgen : ∀ x : 𝕋, ∃ f ∈ Algebra.adjoin 𝒪
        (CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 '' {g | (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ M * r), g = CohCarrier.Gen.U q hq hqL → q ∣ M)}),
      ∀ m : H1 (M * r) ⊤ 𝒪, x • m = f m)
variable (htfull : ∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ M * r), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      ∀ m : H1 (M * r) ⊤ 𝒪, tfull g • m = CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 g m)
variable {𝕋₀ : Type} [CommRing 𝕋₀] [Algebra 𝒪 𝕋₀] [Module 𝕋₀ (H1 M ⊤ 𝒪)] [IsScalarTower 𝒪 𝕋₀ (H1 M ⊤ 𝒪)]
variable (tfull₀ : CohCarrier.Gen M (↑(insert r S) : Set ℕ) → 𝕋₀)
variable (htfull₀ : ∀ g, ∀ m : H1 M ⊤ 𝒪, tfull₀ g • m = CohCarrier.opFamily M ⊤ (↑(insert r S) : Set ℕ) 𝒪 g m)
variable (h1 : LevelLE M (M * r) ⊤ ⊤ 1) (hr' : LevelLE M (M * r) ⊤ ⊤ r)

include hr htfull₀ in
theorem diag_T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ M * r)
    (hℓS' : ℓ ∉ (↑(insert r S) : Set ℕ)) (hℓM : ¬ ℓ ∣ M) (a : H1 M ⊤ 𝒪) :
    CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 (.T ℓ hℓ hℓS hℓL) (iDegL M (M * r) ⊤ ⊤ 1 𝒪 𝒪 h1 a) =
        iDegL M (M * r) ⊤ ⊤ 1 𝒪 𝒪 h1 (tfull₀ (.T ℓ hℓ hℓS' hℓM) • a) ∧
      CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 (.T ℓ hℓ hℓS hℓL) (iDegL M (M * r) ⊤ ⊤ r 𝒪 𝒪 hr' a) =
        iDegL M (M * r) ⊤ ⊤ r 𝒪 𝒪 hr' (tfull₀ (.T ℓ hℓ hℓS' hℓM) • a) := by
  have hℓr : ℓ ≠ r := fun h => hℓL (h ▸ dvd_mul_left r M)
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  constructor
  · rw [htfull₀]
    exact (CohCarrier.iDeg_heckeT_comm_of_coprime h1 (Nat.coprime_one_right ℓ) hℓ hℓL a).symm
  · rw [htfull₀]
    exact (CohCarrier.iDeg_heckeT_comm_of_coprime hr' ((Nat.coprime_primes hℓ hr).mpr hℓr) hℓ hℓL a).symm

include hr hrM htfull₀ in
theorem diag_U (q : ℕ) (hq : q.Prime) (hqL : q ∣ M * r) (hqM : q ∣ M) (a : H1 M ⊤ 𝒪) :
    CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 (.U q hq hqL) (iDegL M (M * r) ⊤ ⊤ 1 𝒪 𝒪 h1 a) =
        iDegL M (M * r) ⊤ ⊤ 1 𝒪 𝒪 h1 (tfull₀ (.U q hq hqM) • a) ∧
      CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 (.U q hq hqL) (iDegL M (M * r) ⊤ ⊤ r 𝒪 𝒪 hr' a) =
        iDegL M (M * r) ⊤ ⊤ r 𝒪 𝒪 hr' (tfull₀ (.U q hq hqM) • a) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hqr : q ≠ r := fun h => hrM (h ▸ hqM)
  constructor
  · rw [htfull₀]
    exact (CohCarrier.iDeg_heckeT_comm_of_dvd h1 (Nat.coprime_one_right q) hqM a).symm
  · rw [htfull₀]
    exact (CohCarrier.iDeg_heckeT_comm_of_dvd hr' ((Nat.coprime_primes hq hr).mpr hqr) hqM a).symm

include hr hrM htfull₀ in

theorem exists_gen_diag (g : CohCarrier.Gen (M * r) (↑S : Set ℕ))
    (hguard : ∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ M * r), g = CohCarrier.Gen.U q hq hqL → q ∣ M) :
    ∃ t₀ : 𝕋₀, ∀ a : H1 M ⊤ 𝒪,
      CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 g (iDegL M (M * r) ⊤ ⊤ 1 𝒪 𝒪 h1 a) =
        iDegL M (M * r) ⊤ ⊤ 1 𝒪 𝒪 h1 (t₀ • a) ∧
      CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 g (iDegL M (M * r) ⊤ ⊤ r 𝒪 𝒪 hr' a) =
        iDegL M (M * r) ⊤ ⊤ r 𝒪 𝒪 hr' (t₀ • a) := by
  cases g with
  | T ℓ hℓ hℓS hℓL =>
    have hℓM : ¬ ℓ ∣ M := fun h => hℓL (dvd_mul_of_dvd_left h r)
    have hℓr : ℓ ≠ r := fun h => hℓL (h ▸ dvd_mul_left r M)
    have hℓS' : ℓ ∉ (↑(insert r S) : Set ℕ) := by
      rw [Finset.coe_insert, Set.mem_insert_iff]; rintro (h | h); exacts [hℓr h, hℓS h]
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    refine ⟨tfull₀ (.T ℓ hℓ hℓS' hℓM), fun a => ⟨?_, ?_⟩⟩
    · rw [htfull₀]
      exact (CohCarrier.iDeg_heckeT_comm_of_coprime h1 (Nat.coprime_one_right ℓ) hℓ hℓL a).symm
    · rw [htfull₀]
      exact (CohCarrier.iDeg_heckeT_comm_of_coprime hr' ((Nat.coprime_primes hℓ hr).mpr hℓr) hℓ hℓL a).symm
  | U q hq hqL =>
    have hqM : q ∣ M := hguard q hq hqL rfl
    haveI : NeZero q := ⟨hq.ne_zero⟩
    have hqr : q ≠ r := fun h => hrM (h ▸ hqM)
    refine ⟨tfull₀ (.U q hq hqM), fun a => ⟨?_, ?_⟩⟩
    · rw [htfull₀]
      exact (CohCarrier.iDeg_heckeT_comm_of_dvd h1 (Nat.coprime_one_right q) hqM a).symm
    · rw [htfull₀]
      exact (CohCarrier.iDeg_heckeT_comm_of_dvd hr' ((Nat.coprime_primes hq hr).mpr hqr) hqM a).symm
  | dia δ =>
    refine ⟨1, fun a => ⟨?_, ?_⟩⟩ <;>
    · rw [one_smul]; exact diamondL_top_apply (M * r) 𝒪 δ _

include hr hrM htfull₀ in

theorem exists_diag_of_mem_adjoin (f : Module.End 𝒪 (H1 (M * r) ⊤ 𝒪))
    (hf : f ∈ Algebra.adjoin 𝒪
        (CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 '' {g | (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ M * r), g = CohCarrier.Gen.U q hq hqL → q ∣ M)})) :
    ∃ t₀ : 𝕋₀, ∀ a : H1 M ⊤ 𝒪,
      f (iDegL M (M * r) ⊤ ⊤ 1 𝒪 𝒪 h1 a) = iDegL M (M * r) ⊤ ⊤ 1 𝒪 𝒪 h1 (t₀ • a) ∧
      f (iDegL M (M * r) ⊤ ⊤ r 𝒪 𝒪 hr' a) = iDegL M (M * r) ⊤ ⊤ r 𝒪 𝒪 hr' (t₀ • a) := by
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact exists_gen_diag hr hrM tfull₀ htfull₀ h1 hr' g hg
  | algebraMap c =>
    refine ⟨algebraMap 𝒪 𝕋₀ c, fun a => ⟨?_, ?_⟩⟩ <;>
    · rw [algebraMap_smul, map_smul, Module.algebraMap_end_apply]
  | add x y _ _ hx hy =>
    obtain ⟨a₀, ha₀⟩ := hx; obtain ⟨b₀, hb₀⟩ := hy
    refine ⟨a₀ + b₀, fun a => ⟨?_, ?_⟩⟩
    · rw [LinearMap.add_apply, (ha₀ a).1, (hb₀ a).1, add_smul, map_add]
    · rw [LinearMap.add_apply, (ha₀ a).2, (hb₀ a).2, add_smul, map_add]
  | mul x y _ _ hx hy =>
    obtain ⟨a₀, ha₀⟩ := hx; obtain ⟨b₀, hb₀⟩ := hy
    refine ⟨a₀ * b₀, fun a => ⟨?_, ?_⟩⟩
    · rw [Module.End.mul_apply, (hb₀ a).1, (ha₀ _).1, mul_smul]
    · rw [Module.End.mul_apply, (hb₀ a).2, (ha₀ _).2, mul_smul]

end diag

end E5SigTr

namespace E5SigTr
section diag2
variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
variable {M r : ℕ} [NeZero M] [NeZero r] [NeZero (M * r)] (hr : r.Prime) (hrM : ¬ r ∣ M) {S : Finset ℕ}
variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 (M * r) ⊤ 𝒪)] [IsScalarTower 𝒪 𝕋 (H1 (M * r) ⊤ 𝒪)]
variable (hgen : ∀ x : 𝕋, ∃ f ∈ Algebra.adjoin 𝒪
        (CohCarrier.opFamily (M * r) ⊤ (↑S : Set ℕ) 𝒪 '' {g | (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ M * r), g = CohCarrier.Gen.U q hq hqL → q ∣ M)}),
      ∀ m : H1 (M * r) ⊤ 𝒪, x • m = f m)
variable {𝕋₀ : Type} [CommRing 𝕋₀] [Algebra 𝒪 𝕋₀] [Module 𝕋₀ (H1 M ⊤ 𝒪)] [IsScalarTower 𝒪 𝕋₀ (H1 M ⊤ 𝒪)]
variable (tfull₀ : CohCarrier.Gen M (↑(insert r S) : Set ℕ) → 𝕋₀)
variable (htfull₀ : ∀ g, ∀ m : H1 M ⊤ 𝒪, tfull₀ g • m = CohCarrier.opFamily M ⊤ (↑(insert r S) : Set ℕ) 𝒪 g m)
variable (h1 : LevelLE M (M * r) ⊤ ⊤ 1) (hr' : LevelLE M (M * r) ⊤ ⊤ r)

include hr hrM hgen htfull₀ in

theorem exists_diag (t : 𝕋) : ∃ t₀ : 𝕋₀, ∀ a : H1 M ⊤ 𝒪,
      t • iDegL M (M * r) ⊤ ⊤ 1 𝒪 𝒪 h1 a = iDegL M (M * r) ⊤ ⊤ 1 𝒪 𝒪 h1 (t₀ • a) ∧
      t • iDegL M (M * r) ⊤ ⊤ r 𝒪 𝒪 hr' a = iDegL M (M * r) ⊤ ⊤ r 𝒪 𝒪 hr' (t₀ • a) := by
  obtain ⟨f, hf, hft⟩ := hgen t
  obtain ⟨t₀, ht₀⟩ := exists_diag_of_mem_adjoin hr hrM tfull₀ htfull₀ h1 hr' f hf
  exact ⟨t₀, fun a => ⟨by rw [hft]; exact (ht₀ a).1, by rw [hft]; exact (ht₀ a).2⟩⟩

end diag2
end E5SigTr

namespace E5SigTr
theorem toCornerRing_surjective' {B : Type} [CommRing B] (Sp : IdempotentSplitting B) (i : Fin Sp.n) :
    Function.Surjective (Sp.toCornerRing i) := by
  intro z
  obtain ⟨_, a, rfl⟩ := z
  exact ⟨a, rfl⟩
end E5SigTr

open E5SigTr in
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

    (L : ℕ) [NeZero L] (hL : L = M * r)

    {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 L ⊤ 𝒪)] [IsScalarTower 𝒪 𝕋 (H1 L ⊤ 𝒪)]
    [Module.Finite 𝒪 𝕋]
    (Sp : IdempotentSplitting 𝕋) (i : Fin Sp.n)
    [Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i))]
    [Module.Free 𝒪 ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i))]
    (tfull : CohCarrier.Gen L (↑S : Set ℕ) → 𝕋) (cfull : CohCarrier.Gen L (↑S : Set ℕ) → 𝒪)

    (hgen : ∀ x : 𝕋, ∃ f ∈ Algebra.adjoin 𝒪
        (CohCarrier.opFamily L ⊤ (↑S : Set ℕ) 𝒪 '' {g | (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M)}),
      ∀ m : H1 L ⊤ 𝒪, x • m = f m)
    (htfull : ∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      ∀ m : H1 L ⊤ 𝒪, tfull g • m = CohCarrier.opFamily L ⊤ (↑S : Set ℕ) 𝒪 g m)
    (hcfull : ∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      tfull g - algebraMap 𝒪 𝕋 (cfull g) ∈ Sp.𝔪 i)
    (hcofull : ∀ v : H1 L ⊤ 𝒪, (∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      ∀ k : ℕ, ∃ n : ℕ, ((tfull g - algebraMap 𝒪 𝕋 (cfull g)) ^ n) • v ∈
        ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 L ⊤ 𝒪))) →
      v ∈ cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i))

    (hcT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ L),
      IsLocalRing.residue 𝒪 (cfull (.T ℓ hℓ hℓS hℓL)) = θ (CuspForm.heckeAlgebra.T hℓ hℓM hℓS))
    (hcU0 : ∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), q ∣ M → q ≠ p → q ^ 2 ∣ M →
      cfull (.U q hq hqL) ∈ IsLocalRing.maximalIdeal 𝒪)
    (hcUp : ∀ (hpL : p ∣ L), p ∣ M → IsUnit (cfull (.U p Fact.out hpL)))
    (hcd : ∀ d : (ZMod L)ˣ, cfull (.dia d) - 1 ∈ IsLocalRing.maximalIdeal 𝒪)

    (hocc : cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i) ≠ ⊥)
    (hfaith : ∀ x : Sp.CornerRing i,
      (∀ m : ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i)), x • m = 0) → x = 0)

    {𝕋₀ : Type} [CommRing 𝕋₀] [Algebra 𝒪 𝕋₀] [Module 𝕋₀ (H1 M ⊤ 𝒪)] [IsScalarTower 𝒪 𝕋₀ (H1 M ⊤ 𝒪)]
    [Module.Finite 𝒪 𝕋₀]
    (Sp₀ : IdempotentSplitting 𝕋₀) (i₀ : Fin Sp₀.n)
    [Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀))]
    [Module.Free 𝒪 ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀))]
    (tfull₀ : CohCarrier.Gen M (↑(insert r S) : Set ℕ) → 𝕋₀) (cfull₀ : CohCarrier.Gen M (↑(insert r S) : Set ℕ) → 𝒪)
    (hgen₀ : ∀ x : 𝕋₀, ∃ f ∈ Algebra.adjoin 𝒪 (Set.range (CohCarrier.opFamily M ⊤ (↑(insert r S) : Set ℕ) 𝒪)),
      ∀ m : H1 M ⊤ 𝒪, x • m = f m)
    (htfull₀ : ∀ g, ∀ m : H1 M ⊤ 𝒪, tfull₀ g • m = CohCarrier.opFamily M ⊤ (↑(insert r S) : Set ℕ) 𝒪 g m)
    (hcfull₀ : ∀ g, tfull₀ g - algebraMap 𝒪 𝕋₀ (cfull₀ g) ∈ Sp₀.𝔪 i₀)
    (hcofull₀ : ∀ v : H1 M ⊤ 𝒪, (∀ g, ∀ k : ℕ, ∃ n : ℕ, ((tfull₀ g - algebraMap 𝒪 𝕋₀ (cfull₀ g)) ^ n) • v ∈
        ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 M ⊤ 𝒪))) →
      v ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀))
    (hocc₀ : cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) ≠ ⊥)
    (hfaith₀ : ∀ x : Sp₀.CornerRing i₀,
      (∀ m : ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀)), x • m = 0) → x = 0)

    (hmatchT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ L)
        (hℓS' : ℓ ∉ (↑(insert r S) : Set ℕ)) (hℓM : ¬ ℓ ∣ M),
      cfull (.T ℓ hℓ hℓS hℓL) = cfull₀ (.T ℓ hℓ hℓS' hℓM))
    (hmatchU : ∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L) (hqM : q ∣ M), cfull (.U q hq hqL) = cfull₀ (.U q hq hqM))
    (hcd₀ : ∀ d : (ZMod M)ˣ, cfull₀ (.dia d) - 1 ∈ IsLocalRing.maximalIdeal 𝒪)

    [NeZero r] (h1 : LevelLE M L ⊤ ⊤ 1) (hr' : LevelLE M L ⊤ ⊤ r)

    (hrig : Module.finrank 𝒪 ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i)) ≤
      2 * Module.finrank 𝒪 ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀))) :

    (∀ v : H1 L ⊤ 𝒪, v ∈ cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i) ↔
      ∃ a b : H1 M ⊤ 𝒪, a ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) ∧
        b ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) ∧
        v = iDegL M L ⊤ ⊤ 1 𝒪 𝒪 h1 a + iDegL M L ⊤ ⊤ r 𝒪 𝒪 hr' b) ∧
    (∀ a b : H1 M ⊤ 𝒪, a ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) →
        b ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) →
        iDegL M L ⊤ ⊤ 1 𝒪 𝒪 h1 a + iDegL M L ⊤ ⊤ r 𝒪 𝒪 hr' b = 0 → a = 0 ∧ b = 0) ∧

    Module.finrank 𝒪 ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i)) =
      2 * Module.finrank 𝒪 ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀)) ∧

    ∃ eR : Sp.CornerRing i ≃ₐ[𝒪] Sp₀.CornerRing i₀,
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ L)
          (hℓS' : ℓ ∉ (↑(insert r S) : Set ℕ)) (hℓM : ¬ ℓ ∣ M),
        eR (Sp.toCornerRing i (tfull (.T ℓ hℓ hℓS hℓL))) = Sp₀.toCornerRing i₀ (tfull₀ (.T ℓ hℓ hℓS' hℓM))) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L) (hqM : q ∣ M),
        eR (Sp.toCornerRing i (tfull (.U q hq hqL))) = Sp₀.toCornerRing i₀ (tfull₀ (.U q hq hqM))) ∧
      (∀ (x : Sp.CornerRing i) (a b : ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀)))
          (v : ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i))),
        (v : H1 L ⊤ 𝒪) = iDegL M L ⊤ ⊤ 1 𝒪 𝒪 h1 (a : H1 M ⊤ 𝒪) + iDegL M L ⊤ ⊤ r 𝒪 𝒪 hr' (b : H1 M ⊤ 𝒪) →
          ((x • v : ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i))) : H1 L ⊤ 𝒪) =
            iDegL M L ⊤ ⊤ 1 𝒪 𝒪 h1 ((eR x • a : ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀))) : H1 M ⊤ 𝒪) +
            iDegL M L ⊤ ⊤ r 𝒪 𝒪 hr' ((eR x • b : ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀))) : H1 M ⊤ 𝒪)) := by
  classical
  subst hL
  haveI : IsLocalRing 𝒪 := inferInstance

  obtain ⟨ϖ, hirr⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  have hϖ : maximalIdeal 𝒪 = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hirr
  have hϖ0 : ϖ ≠ 0 := hirr.ne_zero
  have hϖmem : ϖ ∈ maximalIdeal 𝒪 := by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ

  have S2 : ∀ a : H1 M ⊤ 𝒪, a ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) →
      iDegL M (M * r) ⊤ ⊤ 1 𝒪 𝒪 h1 a ∈ cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp.e i) ∧
      iDegL M (M * r) ⊤ ⊤ r 𝒪 𝒪 hr' a ∈ cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp.e i) := fun a ha =>
    ⟨iDegL_mem_corner hr hrM Sp i tfull cfull htfull hcofull hcd Sp₀ i₀ tfull₀ cfull₀ htfull₀ hcfull₀
        hmatchT hmatchU h1 (Or.inl rfl) a ha,
     iDegL_mem_corner hr hrM Sp i tfull cfull htfull hcofull hcd Sp₀ i₀ tfull₀ cfull₀ htfull₀ hcfull₀
        hmatchT hmatchU hr' (Or.inr rfl) a ha⟩

  have S3 : ∀ a b : H1 M ⊤ 𝒪, a ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) →
      b ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) →
      iDegL M (M * r) ⊤ ⊤ 1 𝒪 𝒪 h1 a + iDegL M (M * r) ⊤ ⊤ r 𝒪 𝒪 hr' b = 0 → a = 0 ∧ b = 0 :=
    fun a b ha hb hab => legs_injective hr hrM ρbar habs S hS θ hθ cfull hcT Sp₀ i₀ tfull₀ cfull₀ htfull₀ hcfull₀
      hmatchT h1 hr' a b ha hb hab

  let CM : Submodule 𝒪 (H1 M ⊤ 𝒪) := (cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀)).restrictScalars 𝒪
  let CL : Submodule 𝒪 (H1 (M * r) ⊤ 𝒪) := (cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp.e i)).restrictScalars 𝒪
  let ι₁ := iDegL M (M * r) ⊤ ⊤ 1 𝒪 𝒪 h1
  let ιr := iDegL M (M * r) ⊤ ⊤ r 𝒪 𝒪 hr'
  let D : Submodule 𝒪 (H1 (M * r) ⊤ 𝒪) := CM.map ι₁ ⊔ CM.map ιr
  have hmemD : ∀ v, v ∈ D ↔ ∃ a b : H1 M ⊤ 𝒪, a ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) ∧
      b ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) ∧ v = ι₁ a + ιr b := by
    intro v
    rw [Submodule.mem_sup]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨a, b, ha, hb, rfl⟩
    · rintro ⟨a, b, ha, hb, rfl⟩
      exact ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
  have hDC : D ≤ CL := by
    intro v hv
    obtain ⟨a, b, ha, hb, rfl⟩ := (hmemD v).mp hv
    exact Submodule.add_mem _ (S2 a ha).1 (S2 b hb).2

  let Φ : (↥CM × ↥CM) →ₗ[𝒪] H1 (M * r) ⊤ 𝒪 :=
    (ι₁ ∘ₗ CM.subtype) ∘ₗ LinearMap.fst 𝒪 _ _ + (ιr ∘ₗ CM.subtype) ∘ₗ LinearMap.snd 𝒪 _ _
  have hΦ : ∀ x : ↥CM × ↥CM, Φ x = ι₁ (x.1 : H1 M ⊤ 𝒪) + ιr (x.2 : H1 M ⊤ 𝒪) := fun _ => rfl
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ hab
    rw [hΦ] at hab
    obtain ⟨ha0, hb0⟩ := S3 a b a.2 b.2 hab
    ext <;> simp [ha0, hb0]
  have hΦrange : LinearMap.range Φ = D := by
    apply le_antisymm
    · rintro _ ⟨⟨a, b⟩, rfl⟩
      exact (hmemD _).mpr ⟨a, b, a.2, b.2, hΦ _⟩
    · intro v hv
      obtain ⟨a, b, ha, hb, rfl⟩ := (hmemD v).mp hv
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hΦ _⟩
  haveI : Module.Finite 𝒪 ↥CM := ‹Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀))›
  haveI : Module.Free 𝒪 ↥CM := ‹Module.Free 𝒪 ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀))›
  have hrankD : Module.finrank 𝒪 ↥D = 2 * Module.finrank 𝒪 ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀)) := by
    rw [← hΦrange, LinearMap.finrank_range_of_inj hΦinj, Module.finrank_prod]
    show Module.finrank 𝒪 ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀)) +
      Module.finrank 𝒪 ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀)) = _
    ring

  obtain ⟨ℓ₀, hℓ, hℓS', hℓM, hℓL, hne⟩ := exists_nonEis_prime_unit hr ρbar habs S hS θ hθ cfull hcT cfull₀ hmatchT
  haveI : NeZero ℓ₀ := ⟨hℓ.ne_zero⟩
  have hsat : ∀ v ∈ CL, ϖ • v ∈ D → v ∈ D := by
    intro v hvC hv
    obtain ⟨a, b, ha, hb, hab⟩ := (hmemD _).mp hv

    have hred : iDeg' M (M * r) ⊤ ⊤ 1 (ResidueField 𝒪) h1 (redH M ⊤ a) +
        iDeg' M (M * r) ⊤ ⊤ r (ResidueField 𝒪) hr' (redH M ⊤ b) = 0 := by
      have := congrArg (redH (M * r) ⊤) hab
      rw [map_smul, smul_H1_residueField_eq_zero _ _ ϖ hϖmem, map_add] at this
      exact this.symm
    have hI := (CohCarrier.isEis_kernel_pair_of_prime 𝒪 (ResidueField 𝒪) ℓ₀ M r h1 hr' levelLE_up_one
      (levelLE_up_r hr) hr hrM hℓ hℓL).1 _ _ hred
    obtain ⟨a', ha', rfl⟩ := exists_eq_smul_of_isEis_redH Sp₀ i₀ tfull₀ cfull₀ htfull₀ hcfull₀ ϖ hϖ hϖ0
      ℓ₀ hℓ hℓS' hℓM hne a ha hI.1
    obtain ⟨b', hb', rfl⟩ := exists_eq_smul_of_isEis_redH Sp₀ i₀ tfull₀ cfull₀ htfull₀ hcfull₀ ϖ hϖ hϖ0
      ℓ₀ hℓ hℓS' hℓM hne b hb hI.2
    have hv' : v = ι₁ a' + ιr b' := by
      apply sub_eq_zero.mp
      apply smul_eq_zero_H1 (M * r) ⊤ ϖ hϖ0
      rw [smul_sub, hab, map_smul, map_smul, smul_add, sub_self]
    exact (hmemD v).mpr ⟨a', b', ha', hb', hv'⟩

  haveI : Module.Finite 𝒪 ↥CL := ‹Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp.e i))›
  have hCD : CL ≤ D := le_of_finrank_le_of_saturated CL D hDC (by rw [hrankD]; exact hrig) ϖ hirr hsat
  have hCDeq : CL = D := le_antisymm hCD hDC
  have S45 : ∀ v : H1 (M * r) ⊤ 𝒪, v ∈ cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp.e i) →
      ∃ a b : H1 M ⊤ 𝒪, a ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) ∧
        b ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) ∧
        v = iDegL M (M * r) ⊤ ⊤ 1 𝒪 𝒪 h1 a + iDegL M (M * r) ⊤ ⊤ r 𝒪 𝒪 hr' b :=
    fun v hv => (hmemD v).mp (hCD hv)
  have Srank : Module.finrank 𝒪 ↥(cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp.e i)) =
      2 * Module.finrank 𝒪 ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀)) := by
    rw [← hrankD]
    exact (LinearEquiv.finrank_eq (LinearEquiv.ofEq CL D hCDeq))

  have hcorner₀ : ∀ (t₀ : 𝕋₀) (a : H1 M ⊤ 𝒪), a ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) →
      ((Sp₀.toCornerRing i₀ t₀ : Sp₀.CornerRing i₀) : 𝕋₀) • a = t₀ • a := by
    intro t₀ a ha
    rw [IdempotentSplitting.coe_toCornerRing, mul_smul, mul_smul, Sp₀.e_smul_coe i₀ ⟨a, ha⟩]
    exact Sp₀.e_smul_coe i₀ ⟨t₀ • a, Submodule.smul_mem _ t₀ ha⟩
  have hcornerL : ∀ (t : 𝕋) (v : H1 (M * r) ⊤ 𝒪), v ∈ cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp.e i) →
      ((Sp.toCornerRing i t : Sp.CornerRing i) : 𝕋) • v = t • v := by
    intro t v hv
    rw [IdempotentSplitting.coe_toCornerRing, mul_smul, mul_smul, Sp.e_smul_coe i ⟨v, hv⟩]
    exact Sp.e_smul_coe i ⟨t • v, Submodule.smul_mem _ t hv⟩

  let P : Sp.CornerRing i → Sp₀.CornerRing i₀ → Prop := fun x y =>
    ∀ a : H1 M ⊤ 𝒪, a ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) →
      (x : 𝕋) • ι₁ a = ι₁ ((y : 𝕋₀) • a) ∧ (x : 𝕋) • ιr a = ιr ((y : 𝕋₀) • a)

  have Pgen : ∀ (t : 𝕋) (t₀ : 𝕋₀), (∀ a : H1 M ⊤ 𝒪,
        t • ι₁ a = ι₁ (t₀ • a) ∧ t • ιr a = ιr (t₀ • a)) →
      P (Sp.toCornerRing i t) (Sp₀.toCornerRing i₀ t₀) := by
    intro t t₀ ht a ha
    rw [hcorner₀ t₀ a ha, hcornerL t _ (S2 a ha).1, hcornerL t _ (S2 a ha).2]
    exact ht a

  have hex : ∀ x : Sp.CornerRing i, ∃ y : Sp₀.CornerRing i₀, P x y := by
    intro x
    obtain ⟨t, rfl⟩ := toCornerRing_surjective' Sp i x
    obtain ⟨t₀, ht₀⟩ := exists_diag hr hrM hgen tfull₀ htfull₀ h1 hr' t
    exact ⟨Sp₀.toCornerRing i₀ t₀, Pgen t t₀ ht₀⟩

  have huniq : ∀ (x : Sp.CornerRing i) (y y' : Sp₀.CornerRing i₀), P x y → P x y' → y = y' := by
    intro x y y' hy hy'
    apply sub_eq_zero.mp
    apply hfaith₀
    intro m
    have hcoe : (((y - y') • m : ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀))) : H1 M ⊤ 𝒪) =
        (y : 𝕋₀) • (m : H1 M ⊤ 𝒪) - (y' : 𝕋₀) • (m : H1 M ⊤ 𝒪) := by
      rw [sub_smul y y' m, AddSubgroupClass.coe_sub, IdempotentSplitting.coe_cornerSmul, IdempotentSplitting.coe_cornerSmul]
    have h0 : ι₁ (((y - y') • m : ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀))) : H1 M ⊤ 𝒪) + ιr 0 = 0 := by
      rw [map_zero, add_zero, hcoe, map_sub, ← (hy m m.2).1, ← (hy' m m.2).1, sub_self]
    have := S3 _ 0 ((y - y') • m).2 (Submodule.zero_mem _) h0
    exact Subtype.ext this.1
  choose F hF using hex
  have hFP : ∀ x y, P x y → F x = y := fun x y h => huniq x (F x) y (hF x) h

  have hF1 : F 1 = 1 := by
    apply hFP
    intro a ha
    rw [IdempotentSplitting.coe_one_cornerRing, IdempotentSplitting.coe_one_cornerRing,
      Sp₀.e_smul_coe i₀ ⟨a, ha⟩]
    exact ⟨Sp.e_smul_coe i ⟨_, (S2 a ha).1⟩, Sp.e_smul_coe i ⟨_, (S2 a ha).2⟩⟩
  have hFmul : ∀ x y, F (x * y) = F x * F y := by
    intro x y
    apply hFP
    intro a ha
    have hya : ((F y : Sp₀.CornerRing i₀) : 𝕋₀) • a ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) :=
      Submodule.smul_mem _ _ ha
    show ((x : 𝕋) * (y : 𝕋)) • ι₁ a = ι₁ ((((F x : Sp₀.CornerRing i₀) : 𝕋₀) * ((F y : Sp₀.CornerRing i₀) : 𝕋₀)) • a) ∧
      ((x : 𝕋) * (y : 𝕋)) • ιr a = ιr ((((F x : Sp₀.CornerRing i₀) : 𝕋₀) * ((F y : Sp₀.CornerRing i₀) : 𝕋₀)) • a)
    rw [mul_smul, mul_smul, mul_smul, (hF y a ha).1, (hF y a ha).2, (hF x _ hya).1, (hF x _ hya).2]
    exact ⟨rfl, rfl⟩
  have hF0 : F 0 = 0 := by
    apply hFP
    intro a ha
    show (0 : 𝕋) • ι₁ a = ι₁ ((0 : 𝕋₀) • a) ∧ (0 : 𝕋) • ιr a = ιr ((0 : 𝕋₀) • a)
    simp
  have hFadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    apply hFP
    intro a ha
    show ((x : 𝕋) + (y : 𝕋)) • ι₁ a = ι₁ ((((F x : Sp₀.CornerRing i₀) : 𝕋₀) + ((F y : Sp₀.CornerRing i₀) : 𝕋₀)) • a) ∧
      ((x : 𝕋) + (y : 𝕋)) • ιr a = ιr ((((F x : Sp₀.CornerRing i₀) : 𝕋₀) + ((F y : Sp₀.CornerRing i₀) : 𝕋₀)) • a)
    rw [add_smul, add_smul, add_smul, map_add, map_add, (hF x a ha).1, (hF x a ha).2, (hF y a ha).1, (hF y a ha).2]
    exact ⟨rfl, rfl⟩
  have hFcomm : ∀ c : 𝒪, F (algebraMap 𝒪 (Sp.CornerRing i) c) = algebraMap 𝒪 (Sp₀.CornerRing i₀) c := by
    intro c
    apply hFP
    apply Pgen
    intro a
    constructor <;> rw [algebraMap_smul, algebraMap_smul, map_smul]
  let Fa : Sp.CornerRing i →ₐ[𝒪] Sp₀.CornerRing i₀ :=
    { toFun := F, map_one' := hF1, map_mul' := hFmul, map_zero' := hF0, map_add' := hFadd, commutes' := hFcomm }
  have hFa : ∀ x, Fa x = F x := fun _ => rfl

  have hinj : Function.Injective Fa := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    apply hfaith
    intro m
    obtain ⟨a, b, ha, hb, hm⟩ := S45 m m.2
    apply Subtype.ext
    rw [IdempotentSplitting.coe_cornerSmul, ZeroMemClass.coe_zero, hm, smul_add, (hF x a ha).1, (hF x b hb).2,
      ← hFa, hx]
    show ι₁ ((0 : 𝕋₀) • a) + ιr ((0 : 𝕋₀) • b) = 0
    simp

  have hsurjgen : ∀ f₀ ∈ Algebra.adjoin 𝒪 (Set.range (CohCarrier.opFamily M ⊤ (↑(insert r S) : Set ℕ) 𝒪)),
      ∃ x : Sp.CornerRing i, ∀ a : H1 M ⊤ 𝒪, a ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) →
        (x : 𝕋) • ι₁ a = ι₁ (f₀ a) ∧ (x : 𝕋) • ιr a = ιr (f₀ a) := by
    intro f₀ hf₀
    induction hf₀ using Algebra.adjoin_induction with
    | mem f hf =>
      obtain ⟨g, rfl⟩ := hf
      cases g with
      | T ℓ hℓ hℓS' hℓM =>
        have hℓS : ℓ ∉ (↑S : Set ℕ) := fun h => hℓS' (by
          rw [Finset.coe_insert, Set.mem_insert_iff]; exact Or.inr h)
        have hℓr : ℓ ≠ r := fun h => hℓS' (by rw [Finset.coe_insert, Set.mem_insert_iff]; exact Or.inl h)
        have hℓL : ¬ ℓ ∣ M * r := fun h => ((Nat.Prime.dvd_mul hℓ).mp h).elim hℓM
          (fun h' => hℓr ((Nat.prime_dvd_prime_iff_eq hℓ hr).mp h'))
        refine ⟨Sp.toCornerRing i (tfull (.T ℓ hℓ hℓS hℓL)), fun a ha => ?_⟩
        have hP := Pgen (tfull (.T ℓ hℓ hℓS hℓL)) (tfull₀ (.T ℓ hℓ hℓS' hℓM)) (fun a => by
          rw [htfull _ (fun q hq hqL h => by cases h), htfull _ (fun q hq hqL h => by cases h)]
          exact diag_T hr tfull₀ htfull₀ h1 hr' ℓ hℓ hℓS hℓL hℓS' hℓM a) a ha
        rw [hP.1, hP.2, hcorner₀ _ a ha, htfull₀]
        exact ⟨rfl, rfl⟩
      | U q hq hqM =>
        have hqL : q ∣ M * r := dvd_mul_of_dvd_left hqM r
        refine ⟨Sp.toCornerRing i (tfull (.U q hq hqL)), fun a ha => ?_⟩
        have hP := Pgen (tfull (.U q hq hqL)) (tfull₀ (.U q hq hqM)) (fun a => by
          rw [htfull _ (fun q' hq' hqL' h => by cases h; exact hqM), htfull _ (fun q' hq' hqL' h => by cases h; exact hqM)]
          exact diag_U hr hrM tfull₀ htfull₀ h1 hr' q hq hqL hqM a) a ha
        rw [hP.1, hP.2, hcorner₀ _ a ha, htfull₀]
        exact ⟨rfl, rfl⟩
      | dia δ =>
        refine ⟨1, fun a ha => ?_⟩
        rw [IdempotentSplitting.coe_one_cornerRing, Sp.e_smul_coe i ⟨_, (S2 a ha).1⟩, Sp.e_smul_coe i ⟨_, (S2 a ha).2⟩]
        show ι₁ a = ι₁ (CohCarrier.diamondL M ⊤ 𝒪 δ a) ∧ ιr a = ιr (CohCarrier.diamondL M ⊤ 𝒪 δ a)
        rw [diamondL_top_apply]
        exact ⟨rfl, rfl⟩
    | algebraMap c =>
      refine ⟨algebraMap 𝒪 _ c, fun a ha => ?_⟩
      have hP := Pgen (algebraMap 𝒪 𝕋 c) (algebraMap 𝒪 𝕋₀ c) (fun a => by
        constructor <;> rw [algebraMap_smul, algebraMap_smul, map_smul]) a ha
      have h1' : Sp.toCornerRing i (algebraMap 𝒪 𝕋 c) = algebraMap 𝒪 (Sp.CornerRing i) c := rfl
      rw [← h1', hP.1, hP.2, hcorner₀ _ a ha, algebraMap_smul, Module.algebraMap_end_apply]
      exact ⟨rfl, rfl⟩
    | add f f' _ _ hx hy =>
      obtain ⟨x, hx⟩ := hx; obtain ⟨x', hx'⟩ := hy
      refine ⟨x + x', fun a ha => ?_⟩
      show ((x : 𝕋) + (x' : 𝕋)) • ι₁ a = ι₁ ((f + f') a) ∧ ((x : 𝕋) + (x' : 𝕋)) • ιr a = ιr ((f + f') a)
      rw [add_smul, add_smul, (hx a ha).1, (hx a ha).2, (hx' a ha).1, (hx' a ha).2,
        LinearMap.add_apply, map_add, map_add]
      exact ⟨rfl, rfl⟩
    | mul f f' hf hf' hx hy =>
      obtain ⟨x, hx⟩ := hx; obtain ⟨x', hx'⟩ := hy
      refine ⟨x * x', fun a ha => ?_⟩
      have hfa : f' a ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) :=
        apply_mem_corner_of_mem_adjoin Sp₀ i₀ hgen₀ hf' a ha
      show ((x : 𝕋) * (x' : 𝕋)) • ι₁ a = ι₁ ((f * f') a) ∧ ((x : 𝕋) * (x' : 𝕋)) • ιr a = ιr ((f * f') a)
      rw [mul_smul, mul_smul, (hx' a ha).1, (hx' a ha).2, (hx _ hfa).1, (hx _ hfa).2, Module.End.mul_apply]
      exact ⟨rfl, rfl⟩
  have hsurj : Function.Surjective Fa := by
    intro y
    obtain ⟨t₀, rfl⟩ := toCornerRing_surjective' Sp₀ i₀ y
    obtain ⟨f₀, hf₀, hft₀⟩ := hgen₀ t₀
    obtain ⟨x, hx⟩ := hsurjgen f₀ hf₀
    refine ⟨x, ?_⟩
    rw [hFa]
    apply hFP
    intro a ha
    rw [hcorner₀ t₀ a ha, hft₀]
    exact hx a ha
  let eR : Sp.CornerRing i ≃ₐ[𝒪] Sp₀.CornerRing i₀ := AlgEquiv.ofBijective Fa ⟨hinj, hsurj⟩
  have heR : ∀ x, eR x = F x := fun _ => rfl
  have S6 : ∃ eR : Sp.CornerRing i ≃ₐ[𝒪] Sp₀.CornerRing i₀,
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ M * r)
          (hℓS' : ℓ ∉ (↑(insert r S) : Set ℕ)) (hℓM : ¬ ℓ ∣ M),
        eR (Sp.toCornerRing i (tfull (.T ℓ hℓ hℓS hℓL))) = Sp₀.toCornerRing i₀ (tfull₀ (.T ℓ hℓ hℓS' hℓM))) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ M * r) (hqM : q ∣ M),
        eR (Sp.toCornerRing i (tfull (.U q hq hqL))) = Sp₀.toCornerRing i₀ (tfull₀ (.U q hq hqM))) ∧
      (∀ (x : Sp.CornerRing i) (a b : ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀)))
          (v : ↥(cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp.e i))),
        (v : H1 (M * r) ⊤ 𝒪) = iDegL M (M * r) ⊤ ⊤ 1 𝒪 𝒪 h1 (a : H1 M ⊤ 𝒪) + iDegL M (M * r) ⊤ ⊤ r 𝒪 𝒪 hr' (b : H1 M ⊤ 𝒪) →
          ((x • v : ↥(cornerSubmodule (M := H1 (M * r) ⊤ 𝒪) (Sp.e i))) : H1 (M * r) ⊤ 𝒪) =
            iDegL M (M * r) ⊤ ⊤ 1 𝒪 𝒪 h1 ((eR x • a : ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀))) : H1 M ⊤ 𝒪) +
            iDegL M (M * r) ⊤ ⊤ r 𝒪 𝒪 hr' ((eR x • b : ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀))) : H1 M ⊤ 𝒪)) := by
    refine ⟨eR, fun ℓ hℓ hℓS hℓL hℓS' hℓM => ?_, fun q hq hqL hqM => ?_, fun x a b v hv => ?_⟩
    · rw [heR]
      apply hFP
      apply Pgen
      intro a
      rw [htfull _ (fun q hq hqL h => by cases h), htfull _ (fun q hq hqL h => by cases h)]
      exact diag_T hr tfull₀ htfull₀ h1 hr' ℓ hℓ hℓS hℓL hℓS' hℓM a
    · rw [heR]
      apply hFP
      apply Pgen
      intro a
      rw [htfull _ (fun q' hq' hqL' h => by cases h; exact hqM), htfull _ (fun q' hq' hqL' h => by cases h; exact hqM)]
      exact diag_U hr hrM tfull₀ htfull₀ h1 hr' q hq hqL hqM a
    · rw [IdempotentSplitting.coe_cornerSmul, hv, smul_add, (hF x a a.2).1, (hF x b b.2).2, heR]
      exact rfl
  obtain ⟨eR, hT, hU, hint⟩ := S6
  refine ⟨fun v => ⟨fun hv => S45 v hv, ?_⟩, fun a b ha hb h => S3 a b ha hb h, Srank, eR, hT, hU, hint⟩
  rintro ⟨a, b, ha, hb, rfl⟩
  exact Submodule.add_mem _ (S2 a ha).1 (S2 b hb).2

end S_CohCarrier_cornerSubmodule_sigmaCorner_gammaZero_auxLevel_eq_iDegL_sup_iDegL
end P2MW
export P2MW.S_CohCarrier_cornerSubmodule_sigmaCorner_gammaZero_auxLevel_eq_iDegL_sup_iDegL (solution)
