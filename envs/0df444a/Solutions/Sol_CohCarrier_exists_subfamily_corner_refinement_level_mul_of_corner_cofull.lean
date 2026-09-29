-- Prove2me | solution 1 for CohCarrier.exists_subfamily_corner_refinement_level_mul_of_corner_cofull
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/5824cab9-e014-5aa1-a091-eed81a01dd35

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CohCarrier_LevelPairing
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CohCarrier_Lower
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_CohCarrier_SubfamilyHeckeData
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_LocalConditions
import Theorems.Thm_CohCarrier_isEis_kernel_pair_of_prime
import Theorems.Thm_CohCarrier_isEis_of_iDeg_add_eq_zero_of_diamond_invariant
import Theorems.Thm_CohCarrier_isUnit_index_of_forall_mem_iff_castHom_eq_one
import Theorems.Thm_CohCarrier_index_comap_unitsMap
import Theorems.Thm_CuspForm_heckeLocal_residue_pi
import Theorems.Thm_ResidualGaloisRep_exists_prime_modEq_one_isFrobeniusAt_eval_charpoly_ne_zero_of_isAbsolutelyIrreducible
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_coprime
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_dvd
import Theorems.Thm_CohCarrier_iDeg_diamondRaw_comm
import Theorems.Thm_CohCarrier_exists_gamma0_heckeT_iDeg_interchange_diamondRaw
import Theorems.Thm_CohCarrier_heckeT_iDeg_q_eq_smul_r
import Theorems.Thm_CohCarrier_levelLE_comap_one_and_q
import Theorems.Thm_CohCarrier_HeckeData_finite_opSubalgebra_and_subsingleton_ML_or_exists_corner
import Theorems.Thm_CohCarrier_HeckeData_nonempty_idempotentSplitting_opSubalgebra
import Theorems.Thm_IharaLemma_map_le_cornerSubmodule_of_adjoin_eq_top_of_forall_exists_partner
import Theorems.Thm_IharaLemma_exists_pow_smul_corner_mem_maximalIdeal_smul
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Theorems.Thm_CohCarrier_opFamily_comm
import Theorems.Thm_IharaLemma_mem_cornerSubmodule_of_forall_exists_pow_sub_algebraMap_smul_mem
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_subfamily_corner_refinement_level_mul_of_corner_cofull
p2m_attr_erase "instance" "Ihara.instGroupIharaAmalgam Ihara.instNormalSpecialLinearGroupFinOfNatNatZAwayPrincipalCongruenceAway FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.zAwayToZMod_algebraMap Ihara.gamma0AwayUnitsChar_coe Ihara.gamma0UnitsHom_coe Ihara.gamma0UnitsChar_apply Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.mennickeA_coe Ihara.mennickeU_coe Ihara.gamma0FinUnitsChar_coe Ihara.gamma0FinMap_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 1600000

open Polynomial IsLocalRing CohCarrier IharaLemma IharaTower
open scoped MatrixGroups IsMulCommutative

namespace PsiStubR

theorem stab_injective
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime)
    (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (r : ℕ) (hr : r.Prime) (hrN : ¬ r ∣ N * p) (hr1 : ¬ p ∣ r - 1)
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ₀ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ₀ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))
    (H₀ : Subgroup (ZMod (N * r))ˣ) [NeZero (N * r)]
    (hH₀ : ∀ v : (ZMod (N * r))ˣ, v ∈ H₀ ↔ ZMod.castHom (dvd_mul_left r N) (ZMod r) (v : ZMod (N * r)) = 1)
    {𝕋₀ : Type} [CommRing 𝕋₀] [Algebra 𝒪 𝕋₀] [Module 𝕋₀ (H1 (N * r) H₀ 𝒪)] [IsScalarTower 𝒪 𝕋₀ (H1 (N * r) H₀ 𝒪)]
    (S₀ : IdempotentSplitting 𝕋₀) (i₀ : Fin S₀.n)
    (e₀ : S₀.CornerRing i₀ ≃ₐ[𝒪] CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ₀)
    (hT₀ : ∀ (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓr : ¬ ℓ ∣ N * r)
        (m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))),
      ((e₀.symm (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) • m
          : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : H1 (N * r) H₀ 𝒪) = heckeT (N * r) H₀ ℓ 𝒪 (m : H1 (N * r) H₀ 𝒪))
    (hdia : ∀ (σ : ↥(CongruenceSubgroup.Gamma0 (N * r))) (v : H1 (N * r) H₀ 𝒪),
      v ∈ cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀) → diamondRaw (N * r) H₀ 𝒪 σ v = v)
    [NeZero (N * r * p)]
    (h1 : LevelLE (N * r) (N * r * p) H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 1)
    (hp' : LevelLE (N * r) (N * r * p) H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) p)
    (αt : S₀.CornerRing i₀)
    (m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)))
    (hm : iDegL (N * r) (N * r * p) H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 1 𝒪 𝒪 h1
        ((αt • m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : H1 (N * r) H₀ 𝒪)
      - iDegL (N * r) (N * r * p) H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) p 𝒪 𝒪 hp' (m : H1 (N * r) H₀ 𝒪) = 0) :
    m = 0 := by
  classical
  set H : Subgroup (ZMod (N * r * p))ˣ := H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p)) with hHdef
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hprN : ¬ p ∣ N * r := by
    intro h
    rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).mp h with h | h
    · exact hpN h
    · have : p = r := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hr).mp h
      exact hrN (this ▸ dvd_mul_left p N)
  have hNr0 : 0 < N * r := Nat.pos_of_ne_zero (NeZero.ne _)
  have hNrp0 : 0 < N * r * p := Nat.pos_of_ne_zero (NeZero.ne _)

  have h₁top : LevelLE (N * r) (N * r * p) (⊤ : Subgroup (ZMod (N * r))ˣ) (⊤ : Subgroup (ZMod (N * r * p))ˣ) 1 :=
    ⟨dvd_mul_right _ _, one_dvd _, fun u _ => Subgroup.mem_top _⟩
  have hqtop : LevelLE (N * r) (N * r * p) (⊤ : Subgroup (ZMod (N * r))ˣ) (⊤ : Subgroup (ZMod (N * r * p))ˣ) p :=
    ⟨dvd_mul_right _ _, by rw [Nat.mul_div_cancel_left p hNr0], fun u _ => Subgroup.mem_top _⟩
  haveI : NeZero (N * r * p * p) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne p)⟩
  have h₁top' : LevelLE (N * r * p) (N * r * p * p) (⊤ : Subgroup (ZMod (N * r * p))ˣ) (⊤ : Subgroup (ZMod (N * r * p * p))ˣ) 1 :=
    ⟨dvd_mul_right _ _, one_dvd _, fun u _ => Subgroup.mem_top _⟩
  have hqtop' : LevelLE (N * r * p) (N * r * p * p) (⊤ : Subgroup (ZMod (N * r * p))ˣ) (⊤ : Subgroup (ZMod (N * r * p * p))ˣ) p :=
    ⟨dvd_mul_right _ _, by rw [Nat.mul_div_cancel_left p hNrp0], fun u _ => Subgroup.mem_top _⟩

  have hunit : IsUnit ((H₀.index : ℕ) : 𝒪) :=
    CohCarrier.isUnit_index_of_forall_mem_iff_castHom_eq_one p hp𝒪 N r hr hr1 H₀ hH₀
  have hunit' : IsUnit ((H.index : ℕ) : 𝒪) := by
    rw [hHdef, CohCarrier.index_comap_unitsMap]; exact hunit

  have hM0 : 0 < N * r * p * ∏ q ∈ S, q :=
    Nat.pos_of_ne_zero (Nat.mul_ne_zero (NeZero.ne _)
      (Finset.prod_ne_zero_iff.mpr (fun q hq => (hS q hq).ne_zero)))
  obtain ⟨ℓ₀, A, σ, hℓ₀, hℓ₀M, -, hA, hσ, hev⟩ :=
    ResidualGaloisRep.exists_prime_modEq_one_isFrobeniusAt_eval_charpoly_ne_zero_of_isAbsolutelyIrreducible
      ρbar habs 1 hM0
  have hℓ₀Nrp : ¬ ℓ₀ ∣ N * r * p := fun h => hℓ₀M (h.mul_right _)
  have hℓ₀Nr : ¬ ℓ₀ ∣ N * r := fun h => hℓ₀Nrp (h.mul_right _)
  have hℓ₀N : ¬ ℓ₀ ∣ N := fun h => hℓ₀Nr (h.mul_right _)
  have hℓ₀S : ℓ₀ ∉ (↑S : Set ℕ) := fun h =>
    hℓ₀M ((Finset.dvd_prod_of_mem (fun q => q) (Finset.mem_coe.mp h)).trans (dvd_mul_left _ _))
  haveI : NeZero ℓ₀ := ⟨hℓ₀.ne_zero⟩

  have hne : θ₀ (CuspForm.heckeAlgebra.T hℓ₀ hℓ₀N hℓ₀S) ≠ (ℓ₀ : ResidueField 𝒪) + 1 := by
    intro heq
    apply hev
    rw [hθ₀ ℓ₀ hℓ₀ hℓ₀N hℓ₀S A hA σ hσ, heq]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow]

  have hihara_top := (CohCarrier.isEis_kernel_pair_of_prime 𝒪 𝒪 ℓ₀ (N * r) p h₁top hqtop h₁top' hqtop'
    (Fact.out : p.Prime) hprN hℓ₀ hℓ₀Nrp).1
  set g : H1 (N * r) H₀ 𝒪 := ((αt • m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : H1 (N * r) H₀ 𝒪) with hgdef
  set h : H1 (N * r) H₀ 𝒪 := -(m : H1 (N * r) H₀ 𝒪) with hhdef
  have hg : ∀ τ : CongruenceSubgroup.Gamma0 (N * r), diamondRaw (N * r) H₀ 𝒪 τ g = g :=
    fun τ => hdia τ g (αt • m).2
  have hh : ∀ τ : CongruenceSubgroup.Gamma0 (N * r), diamondRaw (N * r) H₀ 𝒪 τ h = h := by
    intro τ
    rw [hhdef, map_neg, hdia τ _ m.2]
  have hgh : iDeg' (N * r) (N * r * p) H₀ H 1 𝒪 h1 g + iDeg' (N * r) (N * r * p) H₀ H p 𝒪 hp' h = 0 := by
    rw [hhdef, map_neg, ← sub_eq_add_neg]
    exact hm
  have hEis := (CohCarrier.isEis_of_iDeg_add_eq_zero_of_diamond_invariant 𝒪 𝒪 ℓ₀ (N * r) p H₀ H h1 hp'
    h₁top hqtop hℓ₀ hℓ₀Nrp hunit hunit' hihara_top g h hg hh hgh).2

  have hTm : heckeT (N * r) H₀ ℓ₀ 𝒪 (m : H1 (N * r) H₀ 𝒪) = ((ℓ₀ : 𝒪) + 1) • (m : H1 (N * r) H₀ 𝒪) := by
    have := hEis
    rw [CohCarrier.IsEis, hhdef, map_neg, smul_neg, neg_inj] at this
    exact this

  set t : S₀.CornerRing i₀ := e₀.symm (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ₀ hℓ₀N hℓ₀S)) with htdef
  have hkill : ((t - algebraMap 𝒪 (S₀.CornerRing i₀) ((ℓ₀ : 𝒪) + 1)) • m
      : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) = 0 := by
    have hsub : (t - algebraMap 𝒪 (S₀.CornerRing i₀) ((ℓ₀ : 𝒪) + 1)) • m =
        t • m - algebraMap 𝒪 (S₀.CornerRing i₀) ((ℓ₀ : 𝒪) + 1) • m :=
      sub_smul t (algebraMap 𝒪 (S₀.CornerRing i₀) ((ℓ₀ : 𝒪) + 1)) m
    have halg : algebraMap 𝒪 (S₀.CornerRing i₀) ((ℓ₀ : 𝒪) + 1) • m = ((ℓ₀ : 𝒪) + 1) • m :=
      algebraMap_smul (S₀.CornerRing i₀) ((ℓ₀ : 𝒪) + 1) m
    rw [hsub, halg, sub_eq_zero]
    apply Subtype.ext
    rw [hT₀ ℓ₀ hℓ₀ hℓ₀N hℓ₀S hℓ₀Nr m, hTm]
    exact (Submodule.coe_smul_of_tower _ _).symm

  have hunit_t : IsUnit (t - algebraMap 𝒪 (S₀.CornerRing i₀) ((ℓ₀ : 𝒪) + 1)) := by
    have himg : e₀ (t - algebraMap 𝒪 (S₀.CornerRing i₀) ((ℓ₀ : 𝒪) + 1)) =
        CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ₀ hℓ₀N hℓ₀S)
          - algebraMap 𝒪 _ ((ℓ₀ : 𝒪) + 1) := by
      rw [map_sub, htdef, AlgEquiv.apply_symm_apply, AlgEquiv.commutes]
    suffices hu : IsUnit (e₀ (t - algebraMap 𝒪 (S₀.CornerRing i₀) ((ℓ₀ : 𝒪) + 1))) by
      simpa using hu.map e₀.symm
    rw [himg]
    by_contra hnu
    have hmem := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hres := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [map_sub, CuspForm.heckeLocal.residue_pi, ← IsLocalRing.ResidueField.map_residue, ← map_sub,
      map_eq_zero_iff _ (RingHom.injective _), map_add, map_natCast, map_one, sub_eq_zero] at hres
    exact hne hres
  exact (hunit_t.smul_left_cancel).mp (by rw [hkill, smul_zero])

theorem heckeT_stab_eq_stab_smul
    {𝒪 : Type} [CommRing 𝒪]
    (M q : ℕ) [NeZero M] [NeZero q] [NeZero (M * q)]
    (Hs : Subgroup (ZMod M)ˣ) (Hs' : Subgroup (ZMod (M * q))ˣ)
    (h1 : LevelLE M (M * q) Hs Hs' 1) (hq' : LevelLE M (M * q) Hs Hs' q)
    {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 M Hs 𝒪)] [IsScalarTower 𝒪 𝕋 (H1 M Hs 𝒪)]
    (S₀ : IdempotentSplitting 𝕋) (i₀ : Fin S₀.n)
    (tp αt : S₀.CornerRing i₀)
    (hquad : αt * αt - tp * αt + algebraMap 𝒪 (S₀.CornerRing i₀) (q : 𝒪) = 0)
    (hTp : ∀ m : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀)),
      ((tp • m : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) : H1 M Hs 𝒪) = heckeT M Hs q 𝒪 (m : H1 M Hs 𝒪))
    (hdia : ∀ (σ : ↥(CongruenceSubgroup.Gamma0 M)) (v : H1 M Hs 𝒪),
      v ∈ cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀) → diamondRaw M Hs 𝒪 σ v = v)
    (σ : ↥(CongruenceSubgroup.Gamma0 M))
    (hU1 : ∀ v : H1 M Hs 𝒪, heckeT (M * q) Hs' q 𝒪 (iDeg' M (M * q) Hs Hs' 1 𝒪 h1 v) =
      iDeg' M (M * q) Hs Hs' 1 𝒪 h1 (heckeT M Hs q 𝒪 v) - iDeg' M (M * q) Hs Hs' q 𝒪 hq' (diamondRaw M Hs 𝒪 σ v))
    (hUq : ∀ v : H1 M Hs 𝒪, heckeT (M * q) Hs' q 𝒪 (iDeg' M (M * q) Hs Hs' q 𝒪 hq' v) =
      q • iDeg' M (M * q) Hs Hs' 1 𝒪 h1 v)
    (m : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) :
    heckeT (M * q) Hs' q 𝒪
        (iDegL M (M * q) Hs Hs' 1 𝒪 𝒪 h1 ((αt • m : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) : H1 M Hs 𝒪)
          - iDegL M (M * q) Hs Hs' q 𝒪 𝒪 hq' (m : H1 M Hs 𝒪)) =
      iDegL M (M * q) Hs Hs' 1 𝒪 𝒪 h1 ((αt • (αt • m) : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) : H1 M Hs 𝒪)
        - iDegL M (M * q) Hs Hs' q 𝒪 𝒪 hq' ((αt • m : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) : H1 M Hs 𝒪) := by

  have hL1 : ∀ v : H1 M Hs 𝒪, iDegL M (M * q) Hs Hs' 1 𝒪 𝒪 h1 v = iDeg' M (M * q) Hs Hs' 1 𝒪 h1 v := fun v => rfl
  have hLq : ∀ v : H1 M Hs 𝒪, iDegL M (M * q) Hs Hs' q 𝒪 𝒪 hq' v = iDeg' M (M * q) Hs Hs' q 𝒪 hq' v := fun v => rfl
  simp only [hL1, hLq]
  rw [map_sub, hU1, hUq, hdia σ _ (αt • m).2, ← hTp (αt • m)]

  have hquad' : αt * αt = tp * αt - algebraMap 𝒪 (S₀.CornerRing i₀) (q : 𝒪) := by
    rw [← sub_eq_zero, ← hquad]; ring
  have hq2 : ((αt • (αt • m) : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) : H1 M Hs 𝒪) =
      ((tp • (αt • m) : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) : H1 M Hs 𝒪) - q • (m : H1 M Hs 𝒪) := by
    have h3 : αt • (αt • m) = tp • (αt • m) - algebraMap 𝒪 (S₀.CornerRing i₀) (q : 𝒪) • m := by
      rw [← mul_smul αt αt m, ← mul_smul tp αt m, hquad']
      exact sub_smul (tp * αt) (algebraMap 𝒪 (S₀.CornerRing i₀) (q : 𝒪)) m
    have h4 : algebraMap 𝒪 (S₀.CornerRing i₀) (q : 𝒪) • m = (q : 𝒪) • m :=
      algebraMap_smul (S₀.CornerRing i₀) (q : 𝒪) m
    rw [h3, h4, Submodule.coe_sub, Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul]
  rw [hq2, map_sub, map_nsmul]
  abel

end PsiStubR

namespace OccE4

theorem algebraMap_mem_of_mem_maximalIdeal {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {B : Type} [CommRing B] [Algebra 𝒪 B] [Module.Finite 𝒪 B]
    (J : Ideal B) [hJ : J.IsMaximal] {a : 𝒪} (ha : a ∈ maximalIdeal 𝒪) : algebraMap 𝒪 B a ∈ J := by
  have hmax : (J.comap (algebraMap 𝒪 B)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal J
  have heq : J.comap (algebraMap 𝒪 B) = maximalIdeal 𝒪 := IsLocalRing.eq_maximalIdeal hmax
  have : a ∈ J.comap (algebraMap 𝒪 B) := heq ▸ ha
  exact this

noncomputable def localSplitting (R : Type) [CommRing R] [IsLocalRing R] : IdempotentSplitting R where
  n := 1
  e := fun _ => 1
  𝔪 := fun _ => maximalIdeal R
  coi := CompleteOrthogonalIdempotents.unique_iff.mpr rfl
  isMaximal := fun _ => maximalIdeal.isMaximal R
  exists_eq := fun _ hI => ⟨⟨0, Nat.one_pos⟩, (IsLocalRing.eq_maximalIdeal hI).symm⟩
  mem_iff := fun i j =>
    ⟨fun h => ((maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ h isUnit_one)).elim,
     fun h => (h (Subsingleton.elim i j)).elim⟩

def idx0 (R : Type) [CommRing R] [IsLocalRing R] : Fin (localSplitting R).n := ⟨0, Nat.one_pos⟩

theorem mem_corner_local (R : Type) [CommRing R] [IsLocalRing R] {V : Type} [AddCommGroup V] [Module R V]
    (v : V) : v ∈ cornerSubmodule (M := V) ((localSplitting R).e (idx0 R)) :=
  ⟨v, one_smul R v⟩

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

end OccE4

namespace OccE4

theorem isMaximal_comap_algHom {𝒪 : Type} [CommRing 𝒪] {A B : Type} [CommRing A] [CommRing B]
    [Algebra 𝒪 A] [Algebra 𝒪 B] [Module.Finite 𝒪 B] (ι : A →ₐ[𝒪] B) (I : Ideal B) [hI : I.IsMaximal] :
    (I.comap ι).IsMaximal := by
  letI : Algebra A B := ι.toRingHom.toAlgebra
  haveI : IsScalarTower 𝒪 A B := IsScalarTower.of_algebraMap_eq (fun c => (ι.commutes c).symm)
  haveI : Algebra.IsIntegral 𝒪 B := Algebra.IsIntegral.of_finite 𝒪 B
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.tower_top 𝒪
  have h : (I.comap (algebraMap A B)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal I
  have e : I.comap ι = I.comap (algebraMap A B) := Ideal.ext fun _ => Iff.rfl
  rw [e]
  exact h

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

theorem pow_sub_smul_intertwine {𝒪 : Type} [CommRing 𝒪]
    {B : Type} [CommRing B] [Algebra 𝒪 B] {R : Type} [CommRing R] [Algebra 𝒪 R]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module B V] [IsScalarTower 𝒪 B V]
    {C : Type} [AddCommGroup C] [Module 𝒪 C] [Module R C] [IsScalarTower 𝒪 R C]
    (f : C →ₗ[𝒪] V) (b : B) (y : R) (hb : ∀ m : C, b • f m = f (y • m)) (c : 𝒪) (n : ℕ) (m : C) :
    ((b - algebraMap 𝒪 B c) ^ n) • f m = f (((y - algebraMap 𝒪 R c) ^ n) • m) := by
  induction n generalizing m with
  | zero => rw [pow_zero, pow_zero, one_smul, one_smul]
  | succ n ih =>
    have hstep : (b - algebraMap 𝒪 B c) • f m = f ((y - algebraMap 𝒪 R c) • m) := by
      rw [sub_smul, hb, algebraMap_smul, ← f.map_smul, ← map_sub, sub_smul, algebraMap_smul]
    rw [pow_succ, mul_smul, hstep, ih, ← mul_smul, ← pow_succ]

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

end OccE4

namespace OccE4

section Family

theorem not_dvd_lift (S : Finset ℕ) (N r p : ℕ) [Fact p.Prime] (hpS : p ∈ S)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ N * r) :
    ¬ ℓ ∣ N * r * p := by
  intro h
  rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h
  · exact hℓM h
  · exact hℓS (((Nat.prime_dvd_prime_iff_eq hℓ Fact.out).mp h) ▸ Finset.mem_coe.mpr hpS)

def phiA (S : Finset ℕ) (N r p : ℕ) [Fact p.Prime] (hpS : p ∈ S) :
    Gen (N * r) (↑S : Set ℕ) ⊕ (ZMod (N * r * p))ˣ → Gen (N * r * p) (↑S : Set ℕ)
  | Sum.inl (.T ℓ hℓ hℓS hℓM) => .T ℓ hℓ hℓS (not_dvd_lift S N r p hpS hℓ hℓS hℓM)
  | Sum.inl (.U q hq hqM) => if q ∣ N then .U q hq (hqM.trans (dvd_mul_right (N * r) p)) else .dia 1
  | Sum.inl (.dia _) => .dia 1
  | Sum.inr d => .dia d

def phi1 (S : Finset ℕ) (N r p : ℕ) [Fact p.Prime] (hpS : p ∈ S) :
    (Gen (N * r) (↑S : Set ℕ) ⊕ (ZMod (N * r * p))ˣ) ⊕ Unit → Gen (N * r * p) (↑S : Set ℕ) :=
  Sum.elim (phiA S N r p hpS) (fun _ => .U p Fact.out (dvd_mul_left p (N * r)))

variable (S : Finset ℕ) (N r p : ℕ) [Fact p.Prime] (hpS : p ∈ S)
  (H : Subgroup (ZMod (N * r * p))ˣ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] [NeZero (N * r * p)]

noncomputable def DA : HeckeData 𝒪 (H1 (N * r * p) H 𝒪) (ResidueField 𝒪) :=
  hdataSub (N * r * p) H (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) (phiA S N r p hpS)
    (fun g h => CohCarrier.opFamily_comm _ 𝒪 _ H _ _) (fun _ => 0)

noncomputable def D1 : HeckeData 𝒪 (H1 (N * r * p) H 𝒪) (ResidueField 𝒪) :=
  hdataSub (N * r * p) H (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) (phi1 S N r p hpS)
    (fun g h => CohCarrier.opFamily_comm _ 𝒪 _ H _ _) (fun _ => 0)

theorem DA_op (x : Gen (N * r) (↑S : Set ℕ) ⊕ (ZMod (N * r * p))ˣ) :
    (DA S N r p hpS H 𝒪).op x = opFamily (N * r * p) H (↑S : Set ℕ) 𝒪 (phiA S N r p hpS x) := rfl

theorem D1_op (x : (Gen (N * r) (↑S : Set ℕ) ⊕ (ZMod (N * r * p))ˣ) ⊕ Unit) :
    (D1 S N r p hpS H 𝒪).op x = opFamily (N * r * p) H (↑S : Set ℕ) 𝒪 (phi1 S N r p hpS x) := rfl

theorem DA_le_D1 : (DA S N r p hpS H 𝒪).opSubalgebra ≤ (D1 S N r p hpS H 𝒪).opSubalgebra := by
  refine Algebra.adjoin_mono ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨Sum.inl x, rfl⟩

noncomputable def iota : ↥(DA S N r p hpS H 𝒪).opSubalgebra →ₐ[𝒪] ↥(D1 S N r p hpS H 𝒪).opSubalgebra :=
  Subalgebra.inclusion (DA_le_D1 S N r p hpS H 𝒪)

noncomputable def tA (g : Gen (N * r) (↑S : Set ℕ)) : ↥(DA S N r p hpS H 𝒪).opSubalgebra :=
  ⟨(DA S N r p hpS H 𝒪).op (Sum.inl g), Algebra.subset_adjoin (Set.mem_range_self _)⟩

noncomputable def dA (d : (ZMod (N * r * p))ˣ) : ↥(DA S N r p hpS H 𝒪).opSubalgebra :=
  ⟨(DA S N r p hpS H 𝒪).op (Sum.inr d), Algebra.subset_adjoin (Set.mem_range_self _)⟩

noncomputable def Up : ↥(D1 S N r p hpS H 𝒪).opSubalgebra :=
  ⟨(D1 S N r p hpS H 𝒪).op (Sum.inr ()), Algebra.subset_adjoin (Set.mem_range_self _)⟩

noncomputable def tfull1 : Gen (N * r * p) (↑S : Set ℕ) → ↥(D1 S N r p hpS H 𝒪).opSubalgebra
  | .T ℓ hℓ hℓS hℓL => iota S N r p hpS H 𝒪 (tA S N r p hpS H 𝒪 (.T ℓ hℓ hℓS (fun h => hℓL (h.mul_right p))))
  | .U q hq _ => if hqN : q ∣ N then iota S N r p hpS H 𝒪 (tA S N r p hpS H 𝒪 (.U q hq (hqN.mul_right r)))
      else Up S N r p hpS H 𝒪
  | .dia d => iota S N r p hpS H 𝒪 (dA S N r p hpS H 𝒪 d)

def cfull1 (cfull : Gen (N * r) (↑S : Set ℕ) → 𝒪) (a₀ : 𝒪) : Gen (N * r * p) (↑S : Set ℕ) → 𝒪
  | .T ℓ hℓ hℓS hℓL => cfull (.T ℓ hℓ hℓS (fun h => hℓL (h.mul_right p)))
  | .U q hq _ => if hqN : q ∣ N then cfull (.U q hq (hqN.mul_right r)) else a₀
  | .dia _ => 1

end Family

section Stab
variable {𝒪 : Type} [CommRing 𝒪] (M q : ℕ) [NeZero M] [NeZero q] [NeZero (M * q)]
  (Hs : Subgroup (ZMod M)ˣ) (Hs' : Subgroup (ZMod (M * q))ˣ)
  (h1 : LevelLE M (M * q) Hs Hs' 1) (hq' : LevelLE M (M * q) Hs Hs' q)
  {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 M Hs 𝒪)] [IsScalarTower 𝒪 𝕋 (H1 M Hs 𝒪)]
  (S₀ : IdempotentSplitting 𝕋) (i₀ : Fin S₀.n) (αt : S₀.CornerRing i₀)

noncomputable def stabL : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀)) →ₗ[𝒪] H1 (M * q) Hs' 𝒪 where
  toFun m := iDegL M (M * q) Hs Hs' 1 𝒪 𝒪 h1 ((αt • m : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) : H1 M Hs 𝒪)
    - iDegL M (M * q) Hs Hs' q 𝒪 𝒪 hq' (m : H1 M Hs 𝒪)
  map_add' m m' := by
    show iDegL _ _ _ _ 1 𝒪 𝒪 h1 ((αt • (m + m') : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) : H1 M Hs 𝒪)
      - iDegL _ _ _ _ q 𝒪 𝒪 hq' ((m + m' : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) : H1 M Hs 𝒪) = _
    rw [smul_add, Submodule.coe_add, Submodule.coe_add, map_add, map_add]
    show _ = (iDegL _ _ _ _ 1 𝒪 𝒪 h1 ((αt • m : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) : H1 M Hs 𝒪)
        - iDegL _ _ _ _ q 𝒪 𝒪 hq' (m : H1 M Hs 𝒪)) +
      (iDegL _ _ _ _ 1 𝒪 𝒪 h1 ((αt • m' : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) : H1 M Hs 𝒪)
        - iDegL _ _ _ _ q 𝒪 𝒪 hq' (m' : H1 M Hs 𝒪))
    abel
  map_smul' c m := by
    have hαc : αt • (c • m) = c • (αt • m) := by
      rw [← algebraMap_smul (S₀.CornerRing i₀) c m, ← mul_smul αt (algebraMap 𝒪 (S₀.CornerRing i₀) c) m,
        mul_comm αt (algebraMap 𝒪 (S₀.CornerRing i₀) c), mul_smul (algebraMap 𝒪 (S₀.CornerRing i₀) c) αt m,
        algebraMap_smul]
    show iDegL _ _ _ _ 1 𝒪 𝒪 h1 ((αt • (c • m) : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) : H1 M Hs 𝒪)
      - iDegL _ _ _ _ q 𝒪 𝒪 hq' ((c • m : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) : H1 M Hs 𝒪) =
      c • (iDegL _ _ _ _ 1 𝒪 𝒪 h1 ((αt • m : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) : H1 M Hs 𝒪)
        - iDegL _ _ _ _ q 𝒪 𝒪 hq' (m : H1 M Hs 𝒪))
    rw [hαc, Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower, map_smul, map_smul, smul_sub]

theorem stabL_apply (m : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) :
    stabL M q Hs Hs' h1 hq' S₀ i₀ αt m =
      iDegL M (M * q) Hs Hs' 1 𝒪 𝒪 h1 ((αt • m : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) : H1 M Hs 𝒪)
        - iDegL M (M * q) Hs Hs' q 𝒪 𝒪 hq' (m : H1 M Hs 𝒪) := rfl

end Stab

noncomputable def pickScalar {G B 𝒪 : Type} [Zero 𝒪] (P : G → Prop) (t : G → B) (c : G → 𝒪) : B → 𝒪 :=
  fun b => by classical exact if h : ∃ g, P g ∧ t g = b then c h.choose else 0

theorem pickScalar_spec {G B 𝒪 : Type} [Zero 𝒪] (P : G → Prop) (t : G → B) (c : G → 𝒪) (g : G)
    (hg : P g) : ∃ g', P g' ∧ t g' = t g ∧ pickScalar P t c (t g) = c g' := by
  classical
  have h : ∃ g', P g' ∧ t g' = t g := ⟨g, hg, rfl⟩
  refine ⟨h.choose, h.choose_spec.1, h.choose_spec.2, ?_⟩
  simp only [pickScalar, dif_pos h]

end OccE4

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (hord : (GaloisRepAdic.ofResidualGaloisRep ρbar).IsOrdinaryAt p)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S)
    (N : ℕ) [NeZero N] [NeZero (N * p)] (hpN : ¬ p ∣ N) (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
        (Smin : Finset ℕ) (hpSmin : p ∈ Smin) (hSmin : Smin ⊆ S)
    (hmin : ∀ q : ℕ, q.Prime → q ≠ p → (q ∈ Smin ↔ ¬ ρbar.IsUnramifiedAt q))
    (hNmin : ∀ q ∈ Smin, q ≠ p → q ∣ N)
    (hNunr : ∀ q : ℕ, q.Prime → q ≠ p → q ∉ Smin → q ∣ N → q ^ 2 ∣ N)
    (htame : ∀ q ∈ Smin, q ≠ p → (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)
    (r : ℕ) (hr : r.Prime) (hr5 : 5 ≤ r) (hrS : r ∉ S) (hrN : ¬ r ∣ N * p) (hr1 : ¬ p ∣ r - 1)

    (hrρ : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime r →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ r →
        LinearMap.trace (ResidueField 𝒪) ρbar.V (ρbar.ρ σ) ^ 2 ≠ ((r : ResidueField 𝒪) + 1) ^ 2)
    [Fact (CuspForm.HasIntegralStructure (N * p) 2)]
    (θ₁ : CuspForm.heckeAlgebra (N * p) 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ₁ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N * p) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ₁ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ₀ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ₀ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))
    (πT₀ : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ₀ →ₐ[𝒪] 𝒪)
    (πT₁ : CuspForm.heckeLocal (N * p) (↑S : Set ℕ) 𝒪 θ₁ →ₐ[𝒪] 𝒪)
    (hπ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓ₁ : ¬ ℓ ∣ N * p) (hℓ₀ : ¬ ℓ ∣ N),
      πT₁ (CuspForm.heckeLocal.π (N * p) (↑S : Set ℕ) 𝒪 θ₁ (CuspForm.heckeAlgebra.T hℓ hℓ₁ hℓS)) =
        πT₀ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ hℓ₀ hℓS)))
    (H₀ : Subgroup (ZMod (N * r))ˣ) [NeZero (N * r)]
    (hH₀ : ∀ v : (ZMod (N * r))ˣ, v ∈ H₀ ↔ ZMod.castHom (dvd_mul_left r N) (ZMod r) (v : ZMod (N * r)) = 1)

    {𝕋₀ : Type} [CommRing 𝕋₀] [Algebra 𝒪 𝕋₀] [Module 𝕋₀ (H1 (N * r) H₀ 𝒪)] [IsScalarTower 𝒪 𝕋₀ (H1 (N * r) H₀ 𝒪)]
    (S₀ : IdempotentSplitting 𝕋₀) (i₀ : Fin S₀.n)
    (e₀ : S₀.CornerRing i₀ ≃ₐ[𝒪] CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ₀)
    [Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))]
    [Module.Free 𝒪 ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))]
    (tp : S₀.CornerRing i₀)
    (hT₀ : ∀ (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓr : ¬ ℓ ∣ N * r)
        (m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))),
      ((e₀.symm (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) • m
          : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : H1 (N * r) H₀ 𝒪) = heckeT (N * r) H₀ ℓ 𝒪 (m : H1 (N * r) H₀ 𝒪))
    (htp : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; IsUnit tp ∧ (∀ m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)),
      ((tp • m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : H1 (N * r) H₀ 𝒪) = heckeT (N * r) H₀ p 𝒪 (m : H1 (N * r) H₀ 𝒪)) ∧
      (∀ m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)),
      ((tp • m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : H1 (N * r) H₀ 𝒪) = heckeTlower (N * r) H₀ p 𝒪 (m : H1 (N * r) H₀ 𝒪)))
    (hocc₀ : Submodule.torsionBySet (S₀.CornerRing i₀) ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)) ↑(RingHom.ker (πT₀.comp e₀.toAlgHom)) ≠ ⊥)
    (hrk₀ : Module.finrank 𝒪 ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)) =
      Module.finrank 𝒪 (Submodule.torsionBySet (S₀.CornerRing i₀) ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))
        ↑(RingHom.ker (πT₀.comp e₀.toAlgHom))) * Module.finrank 𝒪 (S₀.CornerRing i₀))
    (hgen : ∀ t : 𝕋₀, ∃ f ∈ Algebra.adjoin 𝒪 (Set.range (CohCarrier.opFamily (N * r) H₀ (↑S : Set ℕ) 𝒪)),
      ∀ m : H1 (N * r) H₀ 𝒪, t • m = f m)
    (tfull : CohCarrier.Gen (N * r) (↑S : Set ℕ) → 𝕋₀)
    (htfull : ∀ g, (match g with | .U q _ _ => q ∣ N | _ => True) →
      ∀ m : H1 (N * r) H₀ 𝒪, tfull g • m = CohCarrier.opFamily (N * r) H₀ (↑S : Set ℕ) 𝒪 g m)
    (cfull : CohCarrier.Gen (N * r) (↑S : Set ℕ) → 𝒪)
    (hcfull : ∀ g, (match g with | .U q _ _ => q ∣ N | _ => True) →
      tfull g - algebraMap 𝒪 𝕋₀ (cfull g) ∈ S₀.𝔪 i₀)
    (hcofull : ∀ v : H1 (N * r) H₀ 𝒪, (∀ g, (match g with | .U q _ _ => q ∣ N | _ => True) →
      ∀ k : ℕ, ∃ n : ℕ, ((tfull g - algebraMap 𝒪 𝕋₀ (cfull g)) ^ n) • v ∈
        ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 (N * r) H₀ 𝒪))) →
      v ∈ cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))
    (hfaith₀ : ∀ t : S₀.CornerRing i₀, (∀ m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)), t • m = 0) → t = 0)

    (hdia : ∀ (σ : ↥(CongruenceSubgroup.Gamma0 (N * r))) (v : H1 (N * r) H₀ 𝒪),
      v ∈ cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀) → diamondRaw (N * r) H₀ 𝒪 σ v = v)

    (αt : S₀.CornerRing i₀)
    (hαt : IsUnit αt ∧ αt * αt - tp * αt + algebraMap 𝒪 (S₀.CornerRing i₀) (p : 𝒪) = 0 ∧
      αt - tp ∈ (maximalIdeal 𝒪).map (algebraMap 𝒪 (S₀.CornerRing i₀))) :
    ∃ (_ : NeZero (N * r * p)) (H : Subgroup (ZMod (N * r * p))ˣ)
      (_ : H = H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p)))
      (𝕋ₐ 𝕋₁ : Type) (_ : CommRing 𝕋ₐ) (_ : CommRing 𝕋₁) (_ : Algebra 𝒪 𝕋ₐ) (_ : Algebra 𝒪 𝕋₁)
      (_ : Module 𝕋ₐ (H1 (N * r * p) H 𝒪)) (_ : Module 𝕋₁ (H1 (N * r * p) H 𝒪))
      (_ : IsScalarTower 𝒪 𝕋ₐ (H1 (N * r * p) H 𝒪)) (_ : IsScalarTower 𝒪 𝕋₁ (H1 (N * r * p) H 𝒪))
      (_ : Module.Finite 𝒪 𝕋ₐ) (_ : Module.Finite 𝒪 𝕋₁)
      (ι : 𝕋ₐ →ₐ[𝒪] 𝕋₁) (_ : ∀ (t : 𝕋ₐ) (v : H1 (N * r * p) H 𝒪), ι t • v = t • v)
      (U : 𝕋₁) (_ : ∀ v : H1 (N * r * p) H 𝒪, U • v = heckeT (N * r * p) H p 𝒪 v)
      (_ : Algebra.adjoin 𝒪 (Set.range ι ∪ {U}) = ⊤)
      (Sₐ : IdempotentSplitting 𝕋ₐ) (iₐ : Fin Sₐ.n) (S₁ : IdempotentSplitting 𝕋₁) (i₁ : Fin S₁.n)
      (_ : Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (Sₐ.e iₐ)))
      (_ : Module.Free 𝒪 ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (Sₐ.e iₐ)))
      (_ : Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁)))
      (_ : Module.Free 𝒪 ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁)))

      (h₁ₐ : LevelLE (N * r * p) (N * r * p) ⊤ H 1)
      (tA : CohCarrier.Gen (N * r) (↑S : Set ℕ) → 𝕋ₐ) (dA : (ZMod (N * r * p))ˣ → 𝕋ₐ),

      (∀ g : CohCarrier.Gen (N * r) (↑S : Set ℕ), (match g with | .T _ _ _ _ => True | .U q _ _ => q ∣ N | .dia _ => False) →
        ∀ v : H1 (N * r * p) H 𝒪, tA g • v = (match g with
            | .T ℓ hℓ _ _ => (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT (N * r * p) H ℓ 𝒪 v)
            | .U q hq _ => (haveI : NeZero q := ⟨hq.ne_zero⟩; heckeT (N * r * p) H q 𝒪 v)
            | .dia _ => v)) ∧
      (∀ g : CohCarrier.Gen (N * r) (↑S : Set ℕ), (match g with | .T _ _ _ _ => True | .U q _ _ => q ∣ N | .dia _ => False) →
        tA g - algebraMap 𝒪 𝕋ₐ (cfull g) ∈ Sₐ.𝔪 iₐ) ∧
      (∀ (d : (ZMod (N * r * p))ˣ) (v : H1 (N * r * p) H 𝒪), dA d • v = diamondL (N * r * p) H 𝒪 d v) ∧
      (∀ d : (ZMod (N * r * p))ˣ, dA d - 1 ∈ Sₐ.𝔪 iₐ) ∧
      Algebra.adjoin 𝒪 (tA '' {g | (match g with | .T _ _ _ _ => True | .U q _ _ => q ∣ N | .dia _ => False)} ∪ Set.range dA) = ⊤ ∧

      (S₁.𝔪 i₁).comap ι = Sₐ.𝔪 iₐ ∧ U ∉ S₁.𝔪 i₁ ∧

      (∀ a : 𝒪, αt - algebraMap 𝒪 (S₀.CornerRing i₀) a ∈ IsLocalRing.maximalIdeal (S₀.CornerRing i₀) →
        U - algebraMap 𝒪 𝕋₁ a ∈ S₁.𝔪 i₁) ∧
      (∀ v : H1 (N * r * p) H 𝒪, v ∈ cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁) →
        v ∈ cornerSubmodule (M := H1 (N * r * p) H 𝒪) (Sₐ.e iₐ)) ∧

      cornerSubmodule (M := H1 (N * r * p) H 𝒪) (Sₐ.e iₐ) ≠ ⊥ ∧
      cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁) ≠ ⊥ ∧

      (∀ t : 𝕋ₐ, (∀ v : H1 (N * r * p) H 𝒪, t • v = 0) → t = 0) ∧
      (∀ t : 𝕋₁, (∀ v : H1 (N * r * p) H 𝒪, t • v = 0) → t = 0) ∧
      (∀ x : S₁.CornerRing i₁,
        (∀ m : ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁)), x • m = 0) → x = 0) ∧

      (∃ (tfull₁ : CohCarrier.Gen (N * r * p) (↑S : Set ℕ) → 𝕋₁) (cfull₁ : CohCarrier.Gen (N * r * p) (↑S : Set ℕ) → 𝒪),

        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ N * r * p) (hℓM : ¬ ℓ ∣ N * r),
          tfull₁ (.T ℓ hℓ hℓS hℓL) = ι (tA (.T ℓ hℓ hℓS hℓM)) ∧ cfull₁ (.T ℓ hℓ hℓS hℓL) = cfull (.T ℓ hℓ hℓS hℓM)) ∧
        (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p) (hqM : q ∣ N * r), q ∣ N →
          tfull₁ (.U q hq hqL) = ι (tA (.U q hq hqM)) ∧ cfull₁ (.U q hq hqL) = cfull (.U q hq hqM)) ∧
        (∀ (hpL : p ∣ N * r * p), tfull₁ (.U p Fact.out hpL) = U ∧
          αt - algebraMap 𝒪 (S₀.CornerRing i₀) (cfull₁ (.U p Fact.out hpL)) ∈
            IsLocalRing.maximalIdeal (S₀.CornerRing i₀)) ∧
        (∀ d : (ZMod (N * r * p))ˣ, tfull₁ (.dia d) = ι (dA d) ∧ cfull₁ (.dia d) = 1) ∧

        (∀ x : 𝕋₁, ∃ f ∈ Algebra.adjoin 𝒪
            (CohCarrier.opFamily (N * r * p) H (↑S : Set ℕ) 𝒪 '' {g | (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p), g = CohCarrier.Gen.U q hq hqL → q ∣ N * p)}),
          ∀ v : H1 (N * r * p) H 𝒪, x • v = f v) ∧

        (∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p), g = CohCarrier.Gen.U q hq hqL → q ∣ N * p) →
          ∀ v : H1 (N * r * p) H 𝒪, tfull₁ g • v = CohCarrier.opFamily (N * r * p) H (↑S : Set ℕ) 𝒪 g v) ∧
        (∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p), g = CohCarrier.Gen.U q hq hqL → q ∣ N * p) →
          tfull₁ g - algebraMap 𝒪 𝕋₁ (cfull₁ g) ∈ S₁.𝔪 i₁) ∧

        (∀ v : H1 (N * r * p) H 𝒪, (∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p), g = CohCarrier.Gen.U q hq hqL → q ∣ N * p) →
          ∀ k : ℕ, ∃ n : ℕ, ((tfull₁ g - algebraMap 𝒪 𝕋₁ (cfull₁ g)) ^ n) • v ∈
            ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 (N * r * p) H 𝒪))) →
          v ∈ cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁))) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI hNrp : NeZero (N * r * p) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne p)⟩
  obtain ⟨h1, hp'⟩ := CohCarrier.levelLE_comap_one_and_q (N * r) p H₀

  have hpNr : ¬ p ∣ N * r := by
    intro h
    rcases (Nat.Prime.dvd_mul Fact.out).mp h with h | h
    · exact hpN h
    · exact hrN (((Nat.prime_dvd_prime_iff_eq Fact.out hr).mp h) ▸ dvd_mul_left p N)
  have hℓlift : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ (↑S : Set ℕ) → ¬ ℓ ∣ N * r → ¬ ℓ ∣ N * r * p :=
    fun ℓ hℓ hℓS hℓM => OccE4.not_dvd_lift S N r p hpS hℓ hℓS hℓM

  haveI hVfin : Module.Finite 𝒪 (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪) := CohCarrier.H1_moduleFinite (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 𝒪
  have hsep : ∀ v' : (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪),
      (∀ k : ℕ, v' ∈ ((maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪))) → v' = 0 := by
    intro v hv
    have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪))
      (I := maximalIdeal 𝒪) (maximalIdeal.isMaximal 𝒪).ne_top
    have : v ∈ (⨅ i : ℕ, maximalIdeal 𝒪 ^ i • ⊤ : Submodule 𝒪 (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)) :=
      (Submodule.mem_iInf _).mpr hv
    rwa [hK, Submodule.mem_bot] at this

  haveI hfinₐ : Module.Finite 𝒪 ↥(OccE4.DA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪).opSubalgebra :=
    (CohCarrier.HeckeData.finite_opSubalgebra_and_subsingleton_ML_or_exists_corner
      (IsLocalRing.residue_surjective) (OccE4.DA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)).1
  haveI hfin₁ : Module.Finite 𝒪 ↥(OccE4.D1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪).opSubalgebra :=
    (CohCarrier.HeckeData.finite_opSubalgebra_and_subsingleton_ML_or_exists_corner
      (IsLocalRing.residue_surjective) (OccE4.D1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)).1
  have hι : ∀ (t : ↥(OccE4.DA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪).opSubalgebra) (v : (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)), OccE4.iota S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 t • v = t • v := fun _ _ => rfl
  have hU : ∀ v : (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪), OccE4.Up S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 • v = heckeT (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) p 𝒪 v := fun _ => rfl
  have htA_T : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ N * r) (v : (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)),
      OccE4.tA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 (.T ℓ hℓ hℓS hℓM) • v = (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) ℓ 𝒪 v) :=
    fun _ _ _ _ _ => rfl
  have htA_U : ∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ N * r) (hqN : q ∣ N) (v : (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)),
      OccE4.tA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 (.U q hq hqM) • v = (haveI : NeZero q := ⟨hq.ne_zero⟩; heckeT (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) q 𝒪 v) := by
    intro q hq hqM hqN v
    show opFamily (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) (↑S : Set ℕ) 𝒪 (OccE4.phiA S N r p hpS (Sum.inl (.U q hq hqM))) v = _
    simp only [OccE4.phiA, if_pos hqN]
    rfl
  have hdA : ∀ (d : (ZMod (N * r * p))ˣ) (v : (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)), OccE4.dA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 d • v = diamondL (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 d v :=
    fun _ _ => rfl
  have hGₐ : Algebra.adjoin 𝒪 (OccE4.tA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 '' {g | (match g with | .T _ _ _ _ => True | .U q _ _ => q ∣ N | .dia _ => False)} ∪ Set.range (OccE4.dA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)) = ⊤ := by
    refine OccE4.adjoin_eq_top_of_le _ _ ?_
    show Algebra.adjoin 𝒪 (Set.range (OccE4.DA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪).op) ≤ _
    refine Algebra.adjoin_mono ?_
    rintro _ ⟨x, rfl⟩
    rcases x with g | d
    · cases g with
      | T ℓ hℓ hℓS hℓM => exact ⟨OccE4.tA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 (.T ℓ hℓ hℓS hℓM), Or.inl ⟨.T ℓ hℓ hℓS hℓM, Set.mem_setOf.mpr trivial, rfl⟩, rfl⟩
      | U q hq hqM =>
        by_cases hqN : q ∣ N
        · exact ⟨OccE4.tA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 (.U q hq hqM), Or.inl ⟨.U q hq hqM, Set.mem_setOf.mpr hqN, rfl⟩, rfl⟩
        · refine ⟨OccE4.dA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 1, Or.inr ⟨1, rfl⟩, ?_⟩
          show (OccE4.DA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪).op (Sum.inr 1) = (OccE4.DA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪).op (Sum.inl (.U q hq hqM))
          rw [OccE4.DA_op, OccE4.DA_op]
          simp only [OccE4.phiA, if_neg hqN]
      | dia d => exact ⟨OccE4.dA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 1, Or.inr ⟨1, rfl⟩, rfl⟩
    · exact ⟨OccE4.dA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 d, Or.inr ⟨d, rfl⟩, rfl⟩
  have hG₁ : Algebra.adjoin 𝒪 (Set.range (OccE4.iota S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪) ∪ {OccE4.Up S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪}) = ⊤ := by
    refine OccE4.adjoin_eq_top_of_le _ _ ?_
    show Algebra.adjoin 𝒪 (Set.range (OccE4.D1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪).op) ≤ _
    refine Algebra.adjoin_mono ?_
    rintro _ ⟨x, rfl⟩
    rcases x with x | u
    · exact ⟨OccE4.iota S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 ⟨(OccE4.DA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪).op x, Algebra.subset_adjoin (Set.mem_range_self _)⟩, Or.inl ⟨_, rfl⟩, rfl⟩
    · exact ⟨OccE4.Up S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪, Or.inr rfl, rfl⟩

  haveI : Module.Finite 𝒪 (S₀.CornerRing i₀) := Module.Finite.equiv e₀.symm.toLinearEquiv
  obtain ⟨v₀, hv₀ne⟩ : ∃ v₀ : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)), v₀ ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hocc₀
    exact ⟨x, hx0⟩
  have hnil₀ : ∀ x : (S₀.CornerRing i₀), x ∈ maximalIdeal (S₀.CornerRing i₀) → ∀ k : ℕ, ∃ n : ℕ, ∀ m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)),
      ((x ^ n • m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : (H1 (N * r) H₀ 𝒪)) ∈ ((maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 (N * r) H₀ 𝒪)) := by
    intro x hx k
    obtain ⟨n, hn⟩ := IharaLemma.exists_pow_smul_corner_mem_maximalIdeal_smul (𝒪 := 𝒪)
      (OccE4.localSplitting (S₀.CornerRing i₀)) (OccE4.idx0 (S₀.CornerRing i₀)) x hx (V := ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) k
    let incl₀ : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)) →ₗ[𝒪] (H1 (N * r) H₀ 𝒪) :=
      { toFun := fun m => (m : (H1 (N * r) H₀ 𝒪)), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    exact ⟨n, fun m => OccE4.map_mem_pow_smul_top incl₀ _ k (hn m (OccE4.mem_corner_local (S₀.CornerRing i₀) m))⟩
  have hscal₀ : ∀ (t : 𝕋₀) (c : 𝒪), t - algebraMap 𝒪 𝕋₀ c ∈ S₀.𝔪 i₀ →
      S₀.toCornerRing i₀ t - algebraMap 𝒪 (S₀.CornerRing i₀) c ∈ maximalIdeal (S₀.CornerRing i₀) := by
    intro t c htc
    have h1 : algebraMap 𝕋₀ (S₀.CornerRing i₀) (t - algebraMap 𝒪 𝕋₀ c) ∈ maximalIdeal (S₀.CornerRing i₀) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (S₀.CornerRing i₀) (S₀.𝔪 i₀) _).mpr htc
    rw [map_sub, ← IsScalarTower.algebraMap_apply] at h1
    exact h1
  have htc₀_smul : ∀ (x : 𝕋₀) (m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))), ((S₀.toCornerRing i₀ x • m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : (H1 (N * r) H₀ 𝒪)) = x • (m : (H1 (N * r) H₀ 𝒪)) := by
    intro x m
    rw [IdempotentSplitting.coe_cornerSmul, IdempotentSplitting.coe_toCornerRing, mul_smul, mul_smul, S₀.e_smul_coe]
    exact S₀.e_smul_coe i₀ ⟨x • (m : (H1 (N * r) H₀ 𝒪)), Submodule.smul_mem _ x m.2⟩
  have hcommC₀ : ∀ (y₀ : (S₀.CornerRing i₀)) (m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))), y₀ • (αt • m) = αt • (y₀ • m) := fun y₀ m => by
    rw [← mul_smul y₀ αt m, mul_comm y₀ αt, mul_smul αt y₀ m]

  let χ₀ : (S₀.CornerRing i₀) →ₐ[𝒪] 𝒪 := πT₀.comp (e₀ : (S₀.CornerRing i₀) →ₐ[𝒪] CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ₀)
  let a₀ : 𝒪 := χ₀ αt
  have ha₀unit : IsUnit a₀ := hαt.1.map χ₀
  have ha₀ : αt - algebraMap 𝒪 (S₀.CornerRing i₀) a₀ ∈ maximalIdeal (S₀.CornerRing i₀) := by
    by_contra hnu
    have hux : IsUnit (αt - algebraMap 𝒪 (S₀.CornerRing i₀) a₀) := of_not_not fun h => hnu ((mem_maximalIdeal _).mpr h)
    have : χ₀ (αt - algebraMap 𝒪 (S₀.CornerRing i₀) a₀) = 0 := by rw [map_sub, AlgHom.commutes]; exact sub_self _
    exact (hux.map χ₀).ne_zero this

  have hstab_def : ∀ m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)), OccE4.stabL (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp' S₀ i₀ αt m = iDeg' (N * r) (N * r * p) H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 1 𝒪 h1 ((αt • m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : (H1 (N * r) H₀ 𝒪))
      - iDeg' (N * r) (N * r * p) H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) p 𝒪 hp' (m : (H1 (N * r) H₀ 𝒪)) := fun _ => rfl
  have hstab_defL : ∀ m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)), OccE4.stabL (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp' S₀ i₀ αt m = iDegL (N * r) (N * r * p) H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 1 𝒪 𝒪 h1 ((αt • m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : (H1 (N * r) H₀ 𝒪))
      - iDegL (N * r) (N * r * p) H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) p 𝒪 𝒪 hp' (m : (H1 (N * r) H₀ 𝒪)) := fun _ => rfl
  have hw0 : OccE4.stabL (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp' S₀ i₀ αt v₀ ≠ 0 := fun h0 =>
    hv₀ne (PsiStubR.stab_injective p hp𝒪 ρbar habs S hS N hpN r hr hrN hr1 θ₀ hθ₀ H₀ hH₀ S₀ i₀ e₀
      (fun ℓ _ hℓ hℓN hℓS hℓr m => hT₀ ℓ hℓ hℓN hℓS hℓr m) hdia h1 hp' αt v₀ h0)
  have hpart_T : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ N * r) (m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))),
      OccE4.iota S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 (OccE4.tA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 (.T ℓ hℓ hℓS hℓM)) • OccE4.stabL (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp' S₀ i₀ αt m = OccE4.stabL (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp' S₀ i₀ αt (S₀.toCornerRing i₀ (tfull (.T ℓ hℓ hℓS hℓM)) • m) := by
    intro ℓ hℓ hℓS hℓM m
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hℓNrp := hℓlift ℓ hℓ hℓS hℓM
    have hℓp : ℓ ≠ p := fun h => hℓS (h ▸ Finset.mem_coe.mpr hpS)
    have hcop : Nat.Coprime ℓ p := (Nat.coprime_primes hℓ Fact.out).mpr hℓp
    have hy : ∀ m' : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)), ((S₀.toCornerRing i₀ (tfull (.T ℓ hℓ hℓS hℓM)) • m' : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : (H1 (N * r) H₀ 𝒪)) =
        heckeT (N * r) H₀ ℓ 𝒪 (m' : (H1 (N * r) H₀ 𝒪)) := by
      intro m'
      rw [htc₀_smul, htfull _ trivial]
      rfl
    rw [hι, htA_T, hstab_def, hstab_def, map_sub,
      ← CohCarrier.iDeg_heckeT_comm_of_coprime h1 (Nat.coprime_one_right ℓ) hℓ hℓNrp,
      ← CohCarrier.iDeg_heckeT_comm_of_coprime hp' hcop hℓ hℓNrp, ← hy m, ← hy (αt • m), hcommC₀]
  have hpart_U : ∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ N * r) (hqN : q ∣ N) (m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))),
      OccE4.iota S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 (OccE4.tA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 (.U q hq hqM)) • OccE4.stabL (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp' S₀ i₀ αt m = OccE4.stabL (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp' S₀ i₀ αt (S₀.toCornerRing i₀ (tfull (.U q hq hqM)) • m) := by
    intro q hq hqM hqN m
    haveI : NeZero q := ⟨hq.ne_zero⟩
    have hqp : q ≠ p := fun h => hpN (h ▸ hqN)
    have hcop : Nat.Coprime q p := (Nat.coprime_primes hq Fact.out).mpr hqp
    have hy : ∀ m' : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)), ((S₀.toCornerRing i₀ (tfull (.U q hq hqM)) • m' : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : (H1 (N * r) H₀ 𝒪)) =
        heckeT (N * r) H₀ q 𝒪 (m' : (H1 (N * r) H₀ 𝒪)) := by
      intro m'
      rw [htc₀_smul, htfull _ hqN]
      rfl
    rw [hι, htA_U q hq hqM hqN, hstab_def, hstab_def, map_sub,
      ← CohCarrier.iDeg_heckeT_comm_of_dvd h1 (Nat.coprime_one_right q) hqM,
      ← CohCarrier.iDeg_heckeT_comm_of_dvd hp' hcop hqM, ← hy m, ← hy (αt • m), hcommC₀]
  have hT1 : LevelLE (N * r) (N * r * p) (⊤ : Subgroup (ZMod (N * r))ˣ) (⊤ : Subgroup (ZMod (N * r * p))ˣ) 1 :=
    ⟨dvd_mul_right _ _, one_dvd _, fun _ _ => Subgroup.mem_top _⟩
  have hTp : LevelLE (N * r) (N * r * p) (⊤ : Subgroup (ZMod (N * r))ˣ) (⊤ : Subgroup (ZMod (N * r * p))ˣ) p :=
    ⟨dvd_mul_right _ _, by rw [Nat.mul_div_cancel_left p (NeZero.pos (N * r))], fun _ _ => Subgroup.mem_top _⟩
  have hpart_dia : ∀ (d : (ZMod (N * r * p))ˣ) (m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))), OccE4.iota S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 (OccE4.dA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 d) • OccE4.stabL (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp' S₀ i₀ αt m = OccE4.stabL (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp' S₀ i₀ αt ((1 : (S₀.CornerRing i₀)) • m) := by
    intro d m
    rw [one_smul (S₀.CornerRing i₀) m, hι, hdA]
    obtain ⟨σ', hσ'⟩ := CohCarrier.gamma0Units_surjective (N * r * p) d
    have hσ'T : (σ' : SL(2, ℤ)) ∈ GammaH (N * r * p) ⊤ := by rw [CohCarrier.GammaH_top]; exact σ'.2
    have hmem1 := hT1.conjLowerMat_mem ⟨(σ' : SL(2, ℤ)), hσ'T⟩
    have hmemp := hTp.conjLowerMat_mem ⟨(σ' : SL(2, ℤ)), hσ'T⟩
    rw [CohCarrier.GammaH_top] at hmem1 hmemp
    rw [hstab_def, map_sub, CohCarrier.diamondL_eq_diamondRaw (N * r * p) _ 𝒪 d σ' hσ',
      ← CohCarrier.iDeg_diamondRaw_comm h1 σ' (hT1.dvd_entry ⟨_, hσ'T⟩) ⟨_, hmem1⟩ rfl _,
      CohCarrier.diamondL_eq_diamondRaw (N * r * p) _ 𝒪 d σ' hσ',
      ← CohCarrier.iDeg_diamondRaw_comm hp' σ' (hTp.dvd_entry ⟨_, hσ'T⟩) ⟨_, hmemp⟩ rfl _,
      hdia ⟨_, hmem1⟩ _ (αt • m).2, hdia ⟨_, hmemp⟩ _ m.2]
  have hHc : ∀ u : (ZMod (N * r * p))ˣ, u ∈ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) ↔
      ZMod.castHom (dvd_mul_of_dvd_left (dvd_mul_left r N) p) (ZMod r) (u : ZMod (N * r * p)) = 1 := by
    intro u
    rw [Subgroup.mem_comap, hH₀, ZMod.unitsMap_val, ← ZMod.castHom_apply (h := dvd_mul_right (N * r) p)
      (R := ZMod (N * r)), ← RingHom.comp_apply, ZMod.castHom_comp]
  have hr4 : 4 ≤ r := le_trans (by norm_num) hr5
  obtain ⟨σ, -, hσ⟩ := CohCarrier.exists_gamma0_heckeT_iDeg_interchange_diamondRaw (N := N * r) (q := p)
    (A := 𝒪) Fact.out hpNr H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp'
  have hUq : ∀ v : (H1 (N * r) H₀ 𝒪), heckeT (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) p 𝒪 (iDeg' (N * r) (N * r * p) H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) p 𝒪 hp' v) =
      p • iDeg' (N * r) (N * r * p) H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 1 𝒪 h1 v :=
    fun v => CohCarrier.heckeT_iDeg_q_eq_smul_r (N := N * r) (q := p) (A := 𝒪) r (dvd_mul_left r N) hr4
      H₀ hH₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) hHc h1 hp' v
  have hpart_Up : ∀ m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)), OccE4.Up S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 • OccE4.stabL (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp' S₀ i₀ αt m = OccE4.stabL (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp' S₀ i₀ αt (αt • m) := by
    intro m
    rw [hU, hstab_defL, hstab_defL]
    exact PsiStubR.heckeT_stab_eq_stab_smul (𝒪 := 𝒪) (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp' S₀ i₀ tp αt hαt.2.1 htp.2.1
      hdia σ hσ hUq m

  have htopnil : ∀ (b : ↥(OccE4.D1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪).opSubalgebra) (y : (S₀.CornerRing i₀)) (c : 𝒪), (∀ m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)), b • OccE4.stabL (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp' S₀ i₀ αt m = OccE4.stabL (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp' S₀ i₀ αt (y • m)) →
      y - algebraMap 𝒪 (S₀.CornerRing i₀) c ∈ maximalIdeal (S₀.CornerRing i₀) →
      ∀ k : ℕ, ∃ n : ℕ, ((b - algebraMap 𝒪 _ c) ^ n) • OccE4.stabL (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp' S₀ i₀ αt v₀ ∈ ((maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)) := by
    intro b y c hb hyc k
    obtain ⟨n, hn⟩ := hnil₀ _ hyc k
    refine ⟨n, ?_⟩
    rw [OccE4.pow_sub_smul_intertwine (OccE4.stabL (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp' S₀ i₀ αt) b y hb c n v₀, hstab_defL]
    refine sub_mem (OccE4.map_mem_pow_smul_top _ _ k ?_) (OccE4.map_mem_pow_smul_top _ _ k (hn v₀))
    rw [← hcommC₀]
    exact hn (αt • v₀)

  have hpartner : ∀ g : Gen (N * r * p) (↑S : Set ℕ), (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p), g = CohCarrier.Gen.U q hq hqL → q ∣ N * p) →
      ∃ y : (S₀.CornerRing i₀), (∀ m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)), OccE4.tfull1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 g • OccE4.stabL (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp' S₀ i₀ αt m = OccE4.stabL (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp' S₀ i₀ αt (y • m)) ∧
        y - algebraMap 𝒪 (S₀.CornerRing i₀) (OccE4.cfull1 S N r p 𝒪 cfull a₀ g) ∈ maximalIdeal (S₀.CornerRing i₀) := by
    intro g hg
    cases g with
    | T ℓ hℓ hℓS hℓL =>
      exact ⟨_, hpart_T ℓ hℓ hℓS (fun h => hℓL (h.mul_right p)), hscal₀ _ _ (hcfull _ trivial)⟩
    | U q hq hqL =>
      by_cases hqN : q ∣ N
      · refine ⟨S₀.toCornerRing i₀ (tfull (.U q hq (hqN.mul_right r))), ?_, ?_⟩
        · intro m
          simp only [OccE4.tfull1, dif_pos hqN]
          exact hpart_U q hq _ hqN m
        · simp only [OccE4.cfull1, dif_pos hqN]
          exact hscal₀ _ _ (hcfull _ hqN)
      · refine ⟨αt, ?_, ?_⟩
        · intro m
          simp only [OccE4.tfull1, dif_neg hqN]
          exact hpart_Up m
        · simp only [OccE4.cfull1, dif_neg hqN]
          exact ha₀
    | dia d =>
      refine ⟨1, hpart_dia d, ?_⟩
      show (1 : (S₀.CornerRing i₀)) - algebraMap 𝒪 (S₀.CornerRing i₀) 1 ∈ _
      rw [map_one, sub_self]
      exact zero_mem _
  have hnilgen : ∀ g : Gen (N * r * p) (↑S : Set ℕ), (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p), g = CohCarrier.Gen.U q hq hqL → q ∣ N * p) →
      ∀ k : ℕ, ∃ n : ℕ, ((OccE4.tfull1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 g - algebraMap 𝒪 _ (OccE4.cfull1 S N r p 𝒪 cfull a₀ g)) ^ n) • OccE4.stabL (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp' S₀ i₀ αt v₀ ∈
        ((maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)) := by
    intro g hg
    obtain ⟨y, hy, hyc⟩ := hpartner g hg
    exact htopnil _ y _ hy hyc

  obtain ⟨S₁⟩ := CohCarrier.HeckeData.nonempty_idempotentSplitting_opSubalgebra (OccE4.D1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)
  obtain ⟨i₁, hi₁⟩ := OccE4.exists_corner_smul_ne_zero S₁ (OccE4.stabL (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp' S₀ i₀ αt v₀) hw0
  have hcfull₁ : ∀ g : Gen (N * r * p) (↑S : Set ℕ), (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p), g = CohCarrier.Gen.U q hq hqL → q ∣ N * p) →
      OccE4.tfull1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 g - algebraMap 𝒪 _ (OccE4.cfull1 S N r p 𝒪 cfull a₀ g) ∈ S₁.𝔪 i₁ :=
    fun g hg => OccE4.mem_𝔪_of_pow_smul_mem S₁ i₁ (maximalIdeal 𝒪) hsep (OccE4.stabL (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp' S₀ i₀ αt v₀) hi₁ _ (hnilgen g hg)
  have hUa : ∀ a : 𝒪, αt - algebraMap 𝒪 (S₀.CornerRing i₀) a ∈ maximalIdeal (S₀.CornerRing i₀) → OccE4.Up S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 - algebraMap 𝒪 _ a ∈ S₁.𝔪 i₁ :=
    fun a ha => OccE4.mem_𝔪_of_pow_smul_mem S₁ i₁ (maximalIdeal 𝒪) hsep (OccE4.stabL (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp' S₀ i₀ αt v₀) hi₁ _
      (htopnil (OccE4.Up S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪) αt a hpart_Up ha)
  have hUnot : OccE4.Up S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 ∉ S₁.𝔪 i₁ := by
    intro hUm
    have h1 : algebraMap 𝒪 (↥(OccE4.D1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪).opSubalgebra) a₀ ∈ S₁.𝔪 i₁ := by
      have h := (S₁.𝔪 i₁).sub_mem hUm (hUa a₀ ha₀)
      exact (congrArg (· ∈ S₁.𝔪 i₁) (sub_sub_cancel (OccE4.Up S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪) (algebraMap 𝒪 (↥(OccE4.D1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪).opSubalgebra) a₀))).mp h
    exact (S₁.isMaximal i₁).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (ha₀unit.map _))
  have gdT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ N * r * p),
      ∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p), Gen.T ℓ hℓ hℓS hℓL = CohCarrier.Gen.U q hq hqL → q ∣ N * p :=
    by intro _ _ _ _ _ _ _ h; cases h
  have gdD : ∀ (d : (ZMod (N * r * p))ˣ),
      ∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p), (Gen.dia d : Gen (N * r * p) (↑S : Set ℕ)) = CohCarrier.Gen.U q hq hqL → q ∣ N * p :=
    by intro _ _ _ _ h; cases h
  have gdU : ∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p), q ∣ N * p →
      ∀ (q' : ℕ) (hq' : q'.Prime) (hqL' : q' ∣ N * r * p), (Gen.U q hq hqL : Gen (N * r * p) (↑S : Set ℕ)) = CohCarrier.Gen.U q' hq' hqL' → q' ∣ N * p := by
    intro q hq hqL h q' hq' hqL' e
    cases e
    exact h
  have hgen₁ : ∀ g : Gen (N * r) (↑S : Set ℕ), (match g with | .T _ _ _ _ => True | .U q _ _ => q ∣ N | .dia _ => False) → OccE4.iota S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 (OccE4.tA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 g) - algebraMap 𝒪 _ (cfull g) ∈ S₁.𝔪 i₁ := by
    intro g hg
    cases g with
    | T ℓ hℓ hℓS hℓM => exact hcfull₁ (.T ℓ hℓ hℓS (hℓlift ℓ hℓ hℓS hℓM)) (gdT _ _ _ _)
    | U q hq hqM =>
      have h := hcfull₁ (.U q hq (hqM.trans (dvd_mul_right _ _))) (gdU _ _ _ (dvd_mul_of_dvd_left hg p))
      simp only [OccE4.tfull1, OccE4.cfull1, dif_pos hg] at h
      exact h
    | dia d => exact absurd hg id
  have hdia₁ : ∀ d : (ZMod (N * r * p))ˣ, OccE4.iota S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 (OccE4.dA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 d) - 1 ∈ S₁.𝔪 i₁ := by
    intro d
    have h := hcfull₁ (.dia d) (gdD d)
    change OccE4.iota S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 (OccE4.dA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 d) - algebraMap 𝒪 (↥(OccE4.D1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪).opSubalgebra) 1 ∈ S₁.𝔪 i₁ at h
    rwa [map_one] at h

  obtain ⟨Sₐ⟩ := CohCarrier.HeckeData.nonempty_idempotentSplitting_opSubalgebra (OccE4.DA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)
  obtain ⟨iₐ, hiₐ⟩ := Sₐ.exists_eq _ (OccE4.isMaximal_comap_algHom (OccE4.iota S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪) (S₁.𝔪 i₁))
  have hmemₐ : ∀ x : ↥(OccE4.DA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪).opSubalgebra, x ∈ Sₐ.𝔪 iₐ ↔ OccE4.iota S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 x ∈ S₁.𝔪 i₁ := by
    intro x
    rw [hiₐ, Ideal.mem_comap]
  have hgenₐ : ∀ g : Gen (N * r) (↑S : Set ℕ), (match g with | .T _ _ _ _ => True | .U q _ _ => q ∣ N | .dia _ => False) → OccE4.tA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 g - algebraMap 𝒪 _ (cfull g) ∈ Sₐ.𝔪 iₐ := by
    intro g hg
    refine (hmemₐ _).mpr ?_
    have E := map_sub (OccE4.iota S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪) (OccE4.tA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 g) (algebraMap 𝒪 _ (cfull g))
    rw [AlgHom.commutes] at E
    exact (congrArg (· ∈ S₁.𝔪 i₁) E).mpr (hgen₁ g hg)
  have hdiaₐ : ∀ d : (ZMod (N * r * p))ˣ, OccE4.dA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 d - 1 ∈ Sₐ.𝔪 iₐ := by
    intro d
    refine (hmemₐ _).mpr ?_
    have E := map_sub (OccE4.iota S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪) (OccE4.dA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 d) 1
    rw [map_one] at E
    exact (congrArg (· ∈ S₁.𝔪 i₁) E).mpr (hdia₁ d)

  have hincl : ∀ v : (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪), v ∈ cornerSubmodule (M := (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)) (S₁.e i₁) → v ∈ cornerSubmodule (M := (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)) (Sₐ.e iₐ) := by
    intro v hv
    refine IharaLemma.map_le_cornerSubmodule_of_adjoin_eq_top_of_forall_exists_partner
      (𝒪 := 𝒪) (LinearMap.id : (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪) →ₗ[𝒪] (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)) S₁ i₁ Sₐ iₐ hsep _ hGₐ ?_ v hv
    rintro g' (⟨g, hg, rfl⟩ | ⟨d, rfl⟩)
    · exact ⟨cfull g, OccE4.iota S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 (OccE4.tA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 g), hgenₐ g hg, hgen₁ g hg, fun v => rfl⟩
    · refine ⟨1, OccE4.iota S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 (OccE4.dA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 d), ?_, ?_, fun v => rfl⟩
      · rw [map_one]; exact hdiaₐ d
      · rw [map_one]; exact hdia₁ d

  have hG₁' : Algebra.adjoin 𝒪 (OccE4.tfull1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 '' {g | (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p), g = CohCarrier.Gen.U q hq hqL → q ∣ N * p)}) = ⊤ := by
    rw [← top_le_iff, ← hG₁]
    refine Algebra.adjoin_le ?_
    rintro x (⟨t, rfl⟩ | hx)
    · have ht : t ∈ Algebra.adjoin 𝒪 (OccE4.tA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 '' {g | (match g with | .T _ _ _ _ => True | .U q _ _ => q ∣ N | .dia _ => False)} ∪ Set.range (OccE4.dA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)) := hGₐ ▸ Algebra.mem_top
      have ht' : OccE4.iota S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 t ∈ (Algebra.adjoin 𝒪 (OccE4.tA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 '' {g | (match g with | .T _ _ _ _ => True | .U q _ _ => q ∣ N | .dia _ => False)} ∪ Set.range (OccE4.dA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪))).map (OccE4.iota S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪) :=
        ⟨t, ht, rfl⟩
      rw [AlgHom.map_adjoin] at ht'
      refine Algebra.adjoin_mono ?_ ht'
      rintro _ ⟨y, hy, rfl⟩
      rcases hy with ⟨g, hg, rfl⟩ | ⟨d, rfl⟩
      · cases g with
        | T ℓ hℓ hℓS hℓM =>
          exact ⟨.T ℓ hℓ hℓS (hℓlift ℓ hℓ hℓS hℓM), Set.mem_setOf.mpr (gdT _ _ _ _), rfl⟩
        | U q hq hqM =>
          refine ⟨.U q hq (hqM.trans (dvd_mul_right _ _)), Set.mem_setOf.mpr (gdU _ _ _ (dvd_mul_of_dvd_left hg p)), ?_⟩
          simp only [OccE4.tfull1, dif_pos (show q ∣ N from hg)]
        | dia d => exact absurd hg id
      · exact ⟨.dia d, Set.mem_setOf.mpr (gdD d), rfl⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      refine Algebra.subset_adjoin ⟨.U p Fact.out (dvd_mul_left p (N * r)), Set.mem_setOf.mpr (gdU _ _ _ (dvd_mul_left p N)), ?_⟩
      simp only [OccE4.tfull1, dif_neg hpN]
  have hcofull₁ : ∀ v : (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪), (∀ g : Gen (N * r * p) (↑S : Set ℕ), (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p), g = CohCarrier.Gen.U q hq hqL → q ∣ N * p) →
      ∀ k : ℕ, ∃ n : ℕ, ((OccE4.tfull1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 g - algebraMap 𝒪 _ (OccE4.cfull1 S N r p 𝒪 cfull a₀ g)) ^ n) • v ∈
        ((maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪))) → v ∈ cornerSubmodule (M := (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)) (S₁.e i₁) := by
    intro v hv
    refine IharaLemma.mem_cornerSubmodule_of_forall_exists_pow_sub_algebraMap_smul_mem hsep S₁ i₁ _ hG₁'
      (OccE4.pickScalar (fun g : Gen (N * r * p) (↑S : Set ℕ) => (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p), g = CohCarrier.Gen.U q hq hqL → q ∣ N * p)) (OccE4.tfull1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪) (OccE4.cfull1 S N r p 𝒪 cfull a₀)) ?_ v ?_
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨g', hg', he, hc⟩ := OccE4.pickScalar_spec (fun g : Gen (N * r * p) (↑S : Set ℕ) => (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p), g = CohCarrier.Gen.U q hq hqL → q ∣ N * p)) (OccE4.tfull1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪) (OccE4.cfull1 S N r p 𝒪 cfull a₀) g hg
      rw [hc, ← he]
      exact hcfull₁ g' hg'
    · rintro _ ⟨g, hg, rfl⟩ k
      obtain ⟨g', hg', he, hc⟩ := OccE4.pickScalar_spec (fun g : Gen (N * r * p) (↑S : Set ℕ) => (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p), g = CohCarrier.Gen.U q hq hqL → q ∣ N * p)) (OccE4.tfull1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪) (OccE4.cfull1 S N r p 𝒪 cfull a₀) g hg
      rw [hc, ← he]
      exact hv g' hg' k
  have hwmem : OccE4.stabL (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp' S₀ i₀ αt v₀ ∈ cornerSubmodule (M := (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)) (S₁.e i₁) := hcofull₁ _ hnilgen
  have hocc₁ : cornerSubmodule (M := (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)) (S₁.e i₁) ≠ ⊥ := fun h =>
    hw0 ((Submodule.eq_bot_iff _).mp h _ hwmem)
  have hoccₐ : cornerSubmodule (M := (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)) (Sₐ.e iₐ) ≠ ⊥ := fun h =>
    hw0 ((Submodule.eq_bot_iff _).mp h _ (hincl _ hwmem))

  have hfaithₐ : ∀ t : ↥(OccE4.DA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪).opSubalgebra, (∀ v : (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪), t • v = 0) → t = 0 :=
    fun t ht => Subtype.ext (LinearMap.ext ht)
  have hfaith₁ : ∀ t : ↥(OccE4.D1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪).opSubalgebra, (∀ v : (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪), t • v = 0) → t = 0 :=
    fun t ht => Subtype.ext (LinearMap.ext ht)
  have hfaithC : ∀ x : S₁.CornerRing i₁,
      (∀ m : ↥(cornerSubmodule (M := (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)) (S₁.e i₁)), x • m = 0) → x = 0 :=
    fun x hx => OccE4.cornerRing_faithful S₁ i₁ hfaith₁ x hx

  have hrelT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ N * r * p) (hℓM : ¬ ℓ ∣ N * r),
      OccE4.tfull1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 (.T ℓ hℓ hℓS hℓL) = OccE4.iota S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 (OccE4.tA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 (.T ℓ hℓ hℓS hℓM)) ∧ OccE4.cfull1 S N r p 𝒪 cfull a₀ (.T ℓ hℓ hℓS hℓL) = cfull (.T ℓ hℓ hℓS hℓM) :=
    fun _ _ _ _ _ => ⟨rfl, rfl⟩
  have hrelU : ∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p) (hqM : q ∣ N * r), q ∣ N →
      OccE4.tfull1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 (.U q hq hqL) = OccE4.iota S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 (OccE4.tA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 (.U q hq hqM)) ∧ OccE4.cfull1 S N r p 𝒪 cfull a₀ (.U q hq hqL) = cfull (.U q hq hqM) := by
    intro q hq hqL hqM hqN
    refine ⟨?_, ?_⟩
    · simp only [OccE4.tfull1, dif_pos hqN]
    · simp only [OccE4.cfull1, dif_pos hqN]
  have hrelp : ∀ (hpL : p ∣ N * r * p), OccE4.tfull1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 (.U p Fact.out hpL) = OccE4.Up S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 ∧
      αt - algebraMap 𝒪 (S₀.CornerRing i₀) (OccE4.cfull1 S N r p 𝒪 cfull a₀ (.U p Fact.out hpL)) ∈ maximalIdeal (S₀.CornerRing i₀) := by
    intro hpL
    refine ⟨?_, ?_⟩
    · simp only [OccE4.tfull1, dif_neg hpN]
    · simp only [OccE4.cfull1, dif_neg hpN]
      exact ha₀
  have hreldia : ∀ d : (ZMod (N * r * p))ˣ, OccE4.tfull1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 (.dia d) = OccE4.iota S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 (OccE4.dA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 d) ∧ OccE4.cfull1 S N r p 𝒪 cfull a₀ (.dia d) = 1 :=
    fun _ => ⟨rfl, rfl⟩
  have hthrough : ∀ x : ↥(OccE4.D1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪).opSubalgebra, ∃ f ∈ Algebra.adjoin 𝒪
      (CohCarrier.opFamily (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) (↑S : Set ℕ) 𝒪 '' {g | (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p), g = CohCarrier.Gen.U q hq hqL → q ∣ N * p)}),
      ∀ v : (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪), x • v = f v := by
    intro x
    refine ⟨(x : Module.End 𝒪 (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)), ?_, fun v => rfl⟩
    have hx : (x : Module.End 𝒪 (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)) ∈ Algebra.adjoin 𝒪 (Set.range (OccE4.D1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪).op) := x.2
    refine Algebra.adjoin_mono ?_ hx
    rintro _ ⟨y, rfl⟩
    rcases y with (g | d) | u
    · cases g with
      | T ℓ hℓ hℓS hℓM => exact ⟨.T ℓ hℓ hℓS (hℓlift ℓ hℓ hℓS hℓM), Set.mem_setOf.mpr (gdT _ _ _ _), rfl⟩
      | U q hq hqM =>
        by_cases hqN : q ∣ N
        · refine ⟨.U q hq (hqM.trans (dvd_mul_right _ _)), Set.mem_setOf.mpr (gdU _ _ _ (dvd_mul_of_dvd_left hqN p)), ?_⟩
          show _ = opFamily (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) _ 𝒪 (OccE4.phiA S N r p hpS (Sum.inl (.U q hq hqM)))
          simp only [OccE4.phiA, if_pos hqN]
        · refine ⟨.dia 1, Set.mem_setOf.mpr (gdD 1), ?_⟩
          show _ = opFamily (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) _ 𝒪 (OccE4.phiA S N r p hpS (Sum.inl (.U q hq hqM)))
          simp only [OccE4.phiA, if_neg hqN]
      | dia d => exact ⟨.dia 1, Set.mem_setOf.mpr (gdD 1), rfl⟩
    · exact ⟨.dia d, Set.mem_setOf.mpr (gdD d), rfl⟩
    · exact ⟨.U p Fact.out (dvd_mul_left p (N * r)), Set.mem_setOf.mpr (gdU _ _ _ (dvd_mul_left p N)), rfl⟩
  have htfull₁ : ∀ g : Gen (N * r * p) (↑S : Set ℕ), (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p), g = CohCarrier.Gen.U q hq hqL → q ∣ N * p) →
      ∀ v : (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪), OccE4.tfull1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 g • v = CohCarrier.opFamily (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) (↑S : Set ℕ) 𝒪 g v := by
    intro g hg v
    cases g with
    | T ℓ hℓ hℓS hℓL => rfl
    | U q hq hqL =>
      by_cases hqN : q ∣ N
      · simp only [OccE4.tfull1, dif_pos hqN]
        rw [hι, htA_U q hq _ hqN]
        rfl
      · have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq Fact.out).mp
          (((Nat.Prime.dvd_mul hq).mp (hg q hq hqL rfl)).resolve_left hqN)
        subst hqp
        simp only [OccE4.tfull1, dif_neg hqN]
        rfl
    | dia d => rfl

  haveI hVtf : Module.IsTorsionFree 𝒪 (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪) := OccE4.isTorsionFree_addMonoidHom (𝒪 := 𝒪) (Additive ↥(GammaH (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p)))))
  obtain ⟨hfinCₐ, hfreeCₐ⟩ := OccE4.finite_and_free_of_submodule (𝒪 := 𝒪) (cornerSubmodule (M := (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)) (Sₐ.e iₐ))
  obtain ⟨hfinC₁, hfreeC₁⟩ := OccE4.finite_and_free_of_submodule (𝒪 := 𝒪) (cornerSubmodule (M := (H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)) (S₁.e i₁))
  refine ⟨hNrp, _, rfl, ↥(OccE4.DA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪).opSubalgebra, ↥(OccE4.D1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪).opSubalgebra, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hfinₐ, hfin₁, OccE4.iota S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪, hι, OccE4.Up S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪, hU, hG₁,
    Sₐ, iₐ, S₁, i₁, hfinCₐ, hfreeCₐ, hfinC₁, hfreeC₁, ⟨dvd_rfl, one_dvd _, fun _ _ => Subgroup.mem_top _⟩,
    OccE4.tA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪, OccE4.dA S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪, ?_, hgenₐ, hdA, hdiaₐ, hGₐ, hiₐ.symm, hUnot, hUa, hincl,
    hoccₐ, hocc₁, hfaithₐ, hfaith₁, hfaithC, OccE4.tfull1 S N r p hpS (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪, OccE4.cfull1 S N r p 𝒪 cfull a₀, hrelT, hrelU, hrelp, hreldia, hthrough, htfull₁,
    hcfull₁, hcofull₁⟩
  intro g hg v
  cases g with
  | T ℓ hℓ hℓS hℓM => exact htA_T ℓ hℓ hℓS hℓM v
  | U q hq hqM => exact htA_U q hq hqM hg v
  | dia d => exact absurd hg id

end S_CohCarrier_exists_subfamily_corner_refinement_level_mul_of_corner_cofull
end P2MW
export P2MW.S_CohCarrier_exists_subfamily_corner_refinement_level_mul_of_corner_cofull (solution)
